import os, re, time, html, json, textwrap, sqlite3
from datetime import datetime, timezone
from urllib.parse import urlparse, parse_qs
import requests
from flask import (
    Flask, render_template, request, session, redirect, url_for, g, jsonify, flash
)
from dotenv import load_dotenv
from bs4 import BeautifulSoup
from werkzeug.security import generate_password_hash, check_password_hash
from functools import wraps
import secrets
import random, string
from zoneinfo import ZoneInfo  # stdlib in Python 3.9+

APP_TZ = os.getenv("APP_TZ", "Asia/Seoul")


# =========================
# App & Config
# =========================
load_dotenv()
app = Flask(__name__)
app.secret_key = os.getenv("SECRET_KEY", "dev-secret-key-change-me")
COMMON_HEADERS = {"User-Agent": "EPICHECK/1.0 (+https://example.edu)"}

# SQLite file path (local)
DB_PATH = os.getenv("EPICHECK_DB", os.path.join(os.path.dirname(__file__), "epicheck.db"))
SUBTHEMES = [
    "basic facts & definitions", "common myths", "who should avoid",
    "possible side effects", "evidence quality", "interactions/contraindications",
    "safe use & moderation", "when to seek professional advice",
    "reliability of sources", "applying guidance for teens",
    "benefits vs. risks", "frequency/duration", "warning signs", "social media claims",
    "long-term effects", "dosage and limits", "age-specific considerations",
    "overhyped benefits", "misleading marketing", "peer pressure and trends",
    "emergency situations", "mixing with other substances", "ethical concerns",
    "influence of celebrities", "online misinformation tactics"
]
ALLOWED_HEALTH_DOMAINS = (
    "who.int", "cdc.gov", "nih.gov", "medlineplus.gov", "ncbi.nlm.nih.gov"
)

QUIZ_SYSTEM = (
    "You are a quiz generator for youth health misinformation topics. "
    "Given a topic, return STRICT JSON: an array of exactly 10 objects. "
    "Each object has: {q (question string), choices (array of 4 strings), answer_idx (0–3), "
    "explain (short rationale), source (credible URL)}. "
    "Ground questions in WHO/CDC/NIH/MedlinePlus sources."
)

# Optional OpenAI (env var required)
try:
    from openai import OpenAI
    _OPENAI_AVAILABLE = True
except Exception:
    _OPENAI_AVAILABLE = False

# feedparser for RSS fallback
try:
    import feedparser
    _FEEDPARSER_AVAILABLE = True
except Exception:
    _FEEDPARSER_AVAILABLE = False

# YouTube transcripts (public/auto captions when available)
try:
    from youtube_transcript_api import (
        YouTubeTranscriptApi,
        TranscriptsDisabled,
        NoTranscriptFound,
        VideoUnavailable,
    )
    _YT_TRANSCRIPT_AVAILABLE = True
except Exception:
    _YT_TRANSCRIPT_AVAILABLE = False


# =========================
# Time helpers (UTC-aware)
# =========================
def _parse_iso_any(value):
    """Best-effort parse of ISO-ish strings to aware UTC datetime."""
    if isinstance(value, datetime):
        dt = value
    else:
        s = str(value or "").strip()
        # handle ...Z
        try:
            dt = datetime.fromisoformat(s.replace("Z", "+00:00"))
        except Exception:
            # fallback common format
            try:
                dt = datetime.strptime(s, "%Y-%m-%d %H:%M:%S")
            except Exception:
                return None
    # normalize to aware UTC
    if dt.tzinfo is None:
        dt = dt.replace(tzinfo=timezone.utc)
    else:
        dt = dt.astimezone(timezone.utc)
    return dt

@app.template_filter("dt")
def jinja_dt(value, fmt="%Y-%m-%d %H:%M"):

    dt = _parse_iso_any(value)
    if not dt:
        return "" if value in (None, "") else str(value)
    try:
        local = dt.astimezone(ZoneInfo(APP_TZ))
    except Exception:
        local = dt  # fallback
    return local.strftime(fmt)

def now_utc():
    return datetime.now(timezone.utc)

def to_aware_utc(dt: datetime | None) -> datetime:
    if dt is None:
        return now_utc()
    if dt.tzinfo is None:
        return dt.replace(tzinfo=timezone.utc)
    return dt.astimezone(timezone.utc)

def iso_now():
    return now_utc().isoformat()

def today_str():
    return now_utc().date().isoformat()


# =========================
# DB helpers (SQLite)
# =========================
def get_db():
    if "db" not in g:
        g.db = sqlite3.connect(DB_PATH, detect_types=sqlite3.PARSE_DECLTYPES)
        g.db.row_factory = sqlite3.Row
    return g.db

@app.teardown_appcontext
def close_db(exc):
    db = g.pop("db", None)
    if db is not None:
        db.close()

def _col_exists(db, table, colname):
    rows = db.execute(f"PRAGMA table_info({table})").fetchall()
    names = {r["name"] for r in rows}
    return colname in names
def init_db():
    db = get_db()
    db.executescript(
        """
        PRAGMA foreign_keys = ON;

        -- ===== Users / Monitoring (existing) =====
        CREATE TABLE IF NOT EXISTS users (
            id            INTEGER PRIMARY KEY AUTOINCREMENT,
            name          TEXT,
            email         TEXT NOT NULL UNIQUE,
            password_hash TEXT NOT NULL,
            created_at    TEXT NOT NULL
        );

        CREATE TABLE IF NOT EXISTS searches (
            id          INTEGER PRIMARY KEY AUTOINCREMENT,
            keywords    TEXT NOT NULL,
            sources     TEXT NOT NULL,
            created_at  TEXT NOT NULL,
            user_id     INTEGER,
            FOREIGN KEY (user_id) REFERENCES users(id) ON DELETE SET NULL
        );

        CREATE TABLE IF NOT EXISTS posts (
            id                  INTEGER PRIMARY KEY AUTOINCREMENT,
            search_id           INTEGER NOT NULL,
            platform            TEXT,
            author              TEXT,
            text                TEXT,
            url                 TEXT,
            video_id            TEXT,
            created_at          TEXT,
            verdict             TEXT,
            credibility_score   REAL,
            explanation         TEXT,
            likes               INTEGER,
            transcript_excerpt  TEXT,
            FOREIGN KEY (search_id) REFERENCES searches(id) ON DELETE CASCADE
        );

        CREATE INDEX IF NOT EXISTS idx_users_email         ON users(email);
        CREATE INDEX IF NOT EXISTS idx_posts_search_id     ON posts(search_id);
        CREATE INDEX IF NOT EXISTS idx_searches_created_at ON searches(created_at);

        -- ===== Quiz persistence =====
        CREATE TABLE IF NOT EXISTS quizzes (
            id         INTEGER PRIMARY KEY AUTOINCREMENT,
            topic      TEXT NOT NULL,
            is_daily   INTEGER NOT NULL DEFAULT 0,  -- 1 for daily quiz
            created_at TEXT NOT NULL
        );

        -- Include 'topic' column for fresh installs
        CREATE TABLE IF NOT EXISTS quiz_items (
            id         INTEGER PRIMARY KEY AUTOINCREMENT,
            quiz_id    INTEGER NOT NULL,
            idx        INTEGER NOT NULL,            -- 0-based order
            q          TEXT NOT NULL,
            choices    TEXT NOT NULL,               -- JSON array of 4 strings
            answer_idx INTEGER NOT NULL,
            explain    TEXT,
            source     TEXT,
            topic      TEXT,                        -- per-item topic (may differ from quizzes.topic)
            FOREIGN KEY (quiz_id) REFERENCES quizzes(id) ON DELETE CASCADE
        );
        CREATE INDEX IF NOT EXISTS idx_quiz_items_quiz ON quiz_items(quiz_id);

        CREATE TABLE IF NOT EXISTS quiz_attempts (
            id         INTEGER PRIMARY KEY AUTOINCREMENT,
            quiz_id    INTEGER NOT NULL,
            user_id    INTEGER,                     -- null for anonymous
            anon_id    TEXT,                        -- per-session token for anonymous
            started_at TEXT NOT NULL,
            finished_at TEXT,
            score      INTEGER NOT NULL DEFAULT 0,
            FOREIGN KEY (quiz_id) REFERENCES quizzes(id) ON DELETE CASCADE,
            FOREIGN KEY (user_id) REFERENCES users(id) ON DELETE SET NULL
        );
        CREATE UNIQUE INDEX IF NOT EXISTS uq_attempt_user ON quiz_attempts(quiz_id, user_id);
        CREATE UNIQUE INDEX IF NOT EXISTS uq_attempt_anon ON quiz_attempts(quiz_id, anon_id);

        CREATE TABLE IF NOT EXISTS quiz_answers (
            id           INTEGER PRIMARY KEY AUTOINCREMENT,
            attempt_id   INTEGER NOT NULL,
            item_id      INTEGER NOT NULL,
            selected_idx INTEGER NOT NULL,
            correct      INTEGER NOT NULL,
            answered_at  TEXT NOT NULL,
            FOREIGN KEY (attempt_id) REFERENCES quiz_attempts(id) ON DELETE CASCADE,
            FOREIGN KEY (item_id)    REFERENCES quiz_items(id)    ON DELETE CASCADE
        );
        CREATE UNIQUE INDEX IF NOT EXISTS uq_answers_attempt_item ON quiz_answers(attempt_id, item_id);

        -- ===== Campaigns =====
        CREATE TABLE IF NOT EXISTS campaigns (
            id         INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id    INTEGER NOT NULL,
            title      TEXT NOT NULL,
            topic      TEXT NOT NULL,
            audience   TEXT NOT NULL,          -- 'school_club' | 'public'
            visibility TEXT NOT NULL,          -- 'private' | 'public'
            starts_on  TEXT NOT NULL,          -- YYYY-MM-DD (UTC date string)
            weeks      INTEGER NOT NULL DEFAULT 4,
            created_at TEXT NOT NULL,
            slug       TEXT NOT NULL UNIQUE,   -- public-friendly id
            FOREIGN KEY (user_id) REFERENCES users(id) ON DELETE CASCADE
        );

        CREATE TABLE IF NOT EXISTS campaign_items (
            id           INTEGER PRIMARY KEY AUTOINCREMENT,
            campaign_id  INTEGER NOT NULL,
            week_no      INTEGER NOT NULL,     -- 1..N
            content_type TEXT NOT NULL,        -- 'myth','quiz','prompt','poster','caption','newsletter'
            title        TEXT NOT NULL,
            body         TEXT NOT NULL,
            sources      TEXT,                 -- JSON array of URLs
            created_at   TEXT NOT NULL,
            FOREIGN KEY (campaign_id) REFERENCES campaigns(id) ON DELETE CASCADE
        );
        CREATE INDEX IF NOT EXISTS idx_campaign_items_campaign ON campaign_items(campaign_id);
        """
    )

    # ---------- Lightweight migrations ----------
    # 1) Add user_id to searches (legacy DBs)
    if not _col_exists(db, "searches", "user_id"):
        db.execute("ALTER TABLE searches ADD COLUMN user_id INTEGER")

    # 2) Ensure quiz_items.topic exists and is indexed; backfill from parent quiz
    if not _col_exists(db, "quiz_items", "topic"):
        db.execute("ALTER TABLE quiz_items ADD COLUMN topic TEXT")
        db.executescript("""
            UPDATE quiz_items
            SET topic = (
                SELECT q.topic FROM quizzes q WHERE q.id = quiz_items.quiz_id
            )
            WHERE topic IS NULL OR topic = '';
        """)
        db.execute("CREATE INDEX IF NOT EXISTS idx_quiz_items_topic ON quiz_items(topic)")

    # 3) Campaigns safety: create tables if missing (older installs)
    #    and ensure 'slug' exists + unique.
    #    If campaigns table exists but slug missing, add and populate.
    if not _col_exists(db, "campaigns", "id"):
        # Table entirely missing -> create both tables (no-op if they already exist)
        db.executescript("""
            CREATE TABLE IF NOT EXISTS campaigns (
                id         INTEGER PRIMARY KEY AUTOINCREMENT,
                user_id    INTEGER NOT NULL,
                title      TEXT NOT NULL,
                topic      TEXT NOT NULL,
                audience   TEXT NOT NULL,
                visibility TEXT NOT NULL,
                starts_on  TEXT NOT NULL,
                weeks      INTEGER NOT NULL DEFAULT 4,
                created_at TEXT NOT NULL,
                slug       TEXT NOT NULL UNIQUE,
                FOREIGN KEY (user_id) REFERENCES users(id) ON DELETE CASCADE
            );
            CREATE TABLE IF NOT EXISTS campaign_items (
                id           INTEGER PRIMARY KEY AUTOINCREMENT,
                campaign_id  INTEGER NOT NULL,
                week_no      INTEGER NOT NULL,
                content_type TEXT NOT NULL,
                title        TEXT NOT NULL,
                body         TEXT NOT NULL,
                sources      TEXT,
                created_at   TEXT NOT NULL,
                FOREIGN KEY (campaign_id) REFERENCES campaigns(id) ON DELETE CASCADE
            );
            CREATE INDEX IF NOT EXISTS idx_campaign_items_campaign ON campaign_items(campaign_id);
        """)
    else:
        # Table exists: check for slug column
        if not _col_exists(db, "campaigns", "slug"):
            db.execute("ALTER TABLE campaigns ADD COLUMN slug TEXT")
            # Backfill a simple unique slug per existing row
            rows = db.execute("SELECT id FROM campaigns WHERE slug IS NULL OR slug = ''").fetchall()
            import secrets, string
            alphabet = "abcdefghjkmnpqrstuvwxyz23456789"
            def gen_slug(n=8):
                return "".join(secrets.choice(alphabet) for _ in range(n))
            for r in rows:
                # ensure uniqueness
                while True:
                    s = gen_slug()
                    exists = db.execute("SELECT 1 FROM campaigns WHERE slug = ?", (s,)).fetchone()
                    if not exists:
                        break
                db.execute("UPDATE campaigns SET slug = ? WHERE id = ?", (s, r["id"]))
            # enforce uniqueness (SQLite requires re-create for full constraint; index is fine here)
            db.execute("CREATE UNIQUE INDEX IF NOT EXISTS uq_campaigns_slug ON campaigns(slug)")

        # Ensure campaign_items table exists (older partial installs)
        if not _col_exists(db, "campaign_items", "id"):
            db.executescript("""
                CREATE TABLE IF NOT EXISTS campaign_items (
                    id           INTEGER PRIMARY KEY AUTOINCREMENT,
                    campaign_id  INTEGER NOT NULL,
                    week_no      INTEGER NOT NULL,
                    content_type TEXT NOT NULL,
                    title        TEXT NOT NULL,
                    body         TEXT NOT NULL,
                    sources      TEXT,
                    created_at   TEXT NOT NULL,
                    FOREIGN KEY (campaign_id) REFERENCES campaigns(id) ON DELETE CASCADE
                );
                CREATE INDEX IF NOT EXISTS idx_campaign_items_campaign ON campaign_items(campaign_id);
            """)

    db.commit()

with app.app_context():
    init_db()

# ---------- User helpers ----------
def get_user_by_email(email: str):
    return get_db().execute("SELECT * FROM users WHERE email = ?", (email,)).fetchone()

def create_user(name: str, email: str, password: str):
    db = get_db()
    pw_hash = generate_password_hash(password)
    db.execute(
        "INSERT INTO users (name, email, password_hash, created_at) VALUES (?, ?, ?, ?)",
        (name, email, pw_hash, iso_now()),
    )
    db.commit()
    return db.execute("SELECT last_insert_rowid()").fetchone()[0]

def authenticate(email: str, password: str):
    row = get_user_by_email(email)
    if not row:
        return None
    if check_password_hash(row["password_hash"], password):
        return row
    return None

@app.before_request
def load_current_user():
    uid = session.get("user_id")
    if uid:
        g.user = get_db().execute("SELECT * FROM users WHERE id = ?", (uid,)).fetchone()
    else:
        g.user = None

@app.context_processor
def inject_user():
    return {"current_user": g.user}

def login_required(fn):
    @wraps(fn)
    def wrapper(*args, **kwargs):
        if not g.user:
            return redirect(url_for("login", next=request.path))
        return fn(*args, **kwargs)
    return wrapper


# =========================
# Persistence for monitor
# =========================
def save_monitor_search(keywords: str, sources_used: list[str], user_id: int | None) -> int:
    """Insert a new row in searches and return its ID."""
    db = get_db()
    db.execute(
        "INSERT INTO searches (keywords, sources, created_at, user_id) VALUES (?, ?, ?, ?)",
        (keywords, ",".join(sources_used), iso_now(), user_id),
    )
    db.commit()
    return db.execute("SELECT last_insert_rowid()").fetchone()[0]

def save_monitor_posts(search_id: int, results: dict):
    rows = []
    for label, items in results.items():
        for p in items:
            rows.append((
                search_id,
                p.get("platform"),
                p.get("author"),
                p.get("text"),
                p.get("url"),
                p.get("video_id"),
                to_aware_utc(p.get("created_at")).isoformat() if p.get("created_at") else None,
                p.get("verdict", label),
                float(p.get("credibility_score")) if p.get("credibility_score") is not None else None,
                p.get("explanation"),
                int(p.get("likes")) if p.get("likes") is not None else None,
                p.get("transcript_excerpt")
            ))
    if not rows:
        return
    db = get_db()
    db.executemany(
        """
        INSERT INTO posts
          (search_id, platform, author, text, url, video_id, created_at,
           verdict, credibility_score, explanation, likes, transcript_excerpt)
        VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
        """,
        rows
    )
    db.commit()


# =========================
# Utilities
# =========================
def clean_html_to_text(html_str, limit=5000):
    soup = BeautifulSoup(html_str or "", "html.parser")
    for tag in soup(["script", "style", "noscript", "header", "footer", "aside", "nav"]):
        tag.decompose()
    text = " ".join(soup.get_text(" ").split())
    return text[:limit]

def fetch_trusted_pages(urls, per_page_limit=5000, max_pages=3):
    texts = []
    for u in urls[:max_pages]:
        try:
            host = urlparse(u).hostname or ""
            if not any(host.endswith(dom) for dom in ALLOWED_HEALTH_DOMAINS):
                continue
            r = safe_get(u, headers=COMMON_HEADERS, timeout=12)
            if not r or not r.text:
                continue
            texts.append({"url": u, "text": clean_html_to_text(r.text, per_page_limit)})
        except Exception:
            continue
    return texts

def _norm(s: str) -> str:
    """Normalize a string to catch near-duplicates."""
    s = (s or "").lower()
    s = s.replace("’", "'").replace("“", '"').replace("”", '"')
    s = re.sub(r"\s+", " ", s)
    s = s.translate(str.maketrans("", "", string.punctuation))
    return s.strip()

def ensure_unique_items(items: list[dict], topic: str) -> list[dict]:
    """Drop near-duplicates by question+choices signature."""
    seen = set()
    out = []
    for it in items:
        qn = _norm(it.get("q",""))
        ch = tuple(_norm(c) for c in (it.get("choices") or []))
        sig = (qn, ch)
        if qn and len(ch) == 4 and sig not in seen:
            seen.add(sig)
            out.append(it)
    return out
def get_attempt_progress(quiz_id: int, attempt_id: int) -> dict[int, dict]:
    """
    Returns { idx: {selected_idx:int, correct:bool, answer_idx:int} }
    """
    db = get_db()
    rows = db.execute(
        """
        SELECT qi.idx, qa.selected_idx, qa.correct, qi.answer_idx
        FROM quiz_answers qa
        JOIN quiz_items qi ON qi.id = qa.item_id
        WHERE qa.attempt_id = ? AND qi.quiz_id = ?
        ORDER BY qi.idx
        """,
        (attempt_id, quiz_id)
    ).fetchall()
    out = {}
    for r in rows:
        out[int(r["idx"])] = {
            "selected_idx": int(r["selected_idx"]),
            "correct": bool(r["correct"]),
            "answer_idx": int(r["answer_idx"]),  # NEW
        }
    return out

def get_or_create_todays_daily(display_topic: str, mix_topics: list[str]) -> int:
    """
    Idempotent “create if not exists” for today’s daily.
    GPT-only generation (with a single broader retry).
    """
    quiz_id = get_daily_quiz_today_id()
    if quiz_id:
        return quiz_id

    # 1) Try GPT on the display topic (e.g., "term1, term2, term3")
    items_gen = gpt_generate_mcqs(display_topic, n_questions=10)

    # 2) If GPT returns <10 or empty, retry once with a broader composite prompt
    if len(items_gen) < 10:
        broader_topic = ", ".join(mix_topics)
        more = gpt_generate_mcqs(broader_topic, n_questions=10)
        items_gen = ensure_unique_items(items_gen + more, topic="__mixed__")

    # 3) If still short, just persist what we have (UI will render however many arrive)
    if not items_gen:
        # Optional: give the user a friendly single item explaining we couldn’t generate today.
        items_gen = [{
            "q": f"Couldn’t generate the daily quiz right now. Try again later.",
            "choices": ["OK", "OK", "OK", "OK"],
            "answer_idx": 0,
            "explain": "Temporary issue creating questions from sources. Please reload in a bit.",
            "source": "https://medlineplus.gov/",
            "topic": display_topic,
        }]

    random.shuffle(items_gen)
    return create_quiz(display_topic, is_daily=True, items=items_gen[:10])
def ensure_ten_mcqs(display_topic: str, mix_topics: list[str], target: int = 10) -> list[dict]:
    """
    Try GPT and OSS first, then GUARANTEE `target` items by backfilling with
    mixed-topic fallbacks. Ensures uniqueness and trims to target.
    """
    items: list[dict] = []

    # 1) GPT on display topic
    items.extend(gpt_generate_mcqs(display_topic, n_questions=target))

    # 2) GPT on broader mix
    if len(items) < target and mix_topics:
        broader_topic = ", ".join([t for t in mix_topics if t]) or display_topic
        more = gpt_generate_mcqs(broader_topic, n_questions=target)
        items = ensure_unique_items(items + more, topic="__mixed__")

    # 3) OSS on display topic (trusted pages)
    if len(items) < target:
        ctx = fetch_trusted_pages(get_trusted_sources_from_session_fallback(display_topic))
        more = oss_generate_mcqs(display_topic, ctx) or []
        items = ensure_unique_items(items + more, topic="__mixed__")

    # 4) OSS on broader mix
    if len(items) < target and mix_topics:
        broader_topic = ", ".join([t for t in mix_topics if t]) or display_topic
        ctx = fetch_trusted_pages(get_trusted_sources_from_session_fallback(broader_topic))
        more = oss_generate_mcqs(broader_topic, ctx) or []
        items = ensure_unique_items(items + more, topic="__mixed__")

    # 5) FINAL GUARANTEE: backfill with mixed-topic synthetic items
    if len(items) < target:
        # prefer user/mix topics, then pad with presets
        topics_pool = [t for t in (mix_topics or []) if t] + [t for t in PRESET_TOPICS]
        # draw small batches until we hit target
        i = 0
        while len(items) < target:
            topic = topics_pool[i % len(topics_pool)]
            need = target - len(items)
            batch = diversified_fallback(topic, n=min(3, need))
            items = ensure_unique_items(items + batch, topic="__mixed__")
            i += 1

    random.shuffle(items)
    return items[:target]

def _balanced_answer_positions(n: int) -> list[int]:
    """Return a list of indices 0..3 roughly balanced across n questions."""
    base = [0,1,2,3] * ((n+3)//4)
    random.shuffle(base)
    return base[:n]
def diversified_fallback(topic: str, n: int = 10) -> list[dict]:
    subthemes = [
        "basic facts & definitions", "common myths", "who should avoid",
        "possible side effects", "evidence quality", "interactions/contraindications",
        "safe use & moderation", "when to seek professional advice",
        "reliability of sources", "applying guidance for teens",
        "benefits vs. risks", "frequency/duration", "warning signs", "social media claims",
        "long-term effects", "dosage and limits", "age-specific considerations",
        "overhyped benefits", "misleading marketing", "peer pressure and trends",
        "emergency situations", "mixing with other substances", "ethical concerns",
        "influence of celebrities", "online misinformation tactics"
    ]

    stems = [
        "Which statement about '{topic}' and {sub} is most accurate?",
        "For teens, what is a safe takeaway regarding '{topic}' and {sub}?",
        "Which claim about '{topic}' and {sub} aligns best with evidence?",
        "What is a reasonable first step if considering '{topic}' related to {sub}?",
        "Which source is most appropriate when evaluating '{topic}' and {sub}?",
        "How should someone verify information about '{topic}' and {sub}?",
        "What is a common misunderstanding about '{topic}' and {sub}?",
        "When learning about '{topic}' and {sub}, what is the safest action?",
        "Which fact about '{topic}' and {sub} would a health expert agree with?",
        "What is the biggest risk to teens when it comes to '{topic}' and {sub}?"
    ]

    distractor_buckets = [
        ["Always safe for everyone.", "Works 100% of the time.", "Replaces medical care.", "Has zero side effects."],
        ["Social media posts are sufficient.", "Personal anecdotes prove efficacy.", "No need to read warnings.",
         "Doctors are unnecessary."],
        ["Immediate results are guaranteed.", "One-size-fits-all dosage works.", "Natural means risk-free.",
         "Label claims are always verified."],
        ["Everyone should try it at least once.", "The more you take, the better.",
         "Health advice on TikTok is always accurate.", "If it's popular, it must be safe."],
        ["There is no risk if it’s natural.", "All studies online are equally reliable.",
         "Side effects only happen to older adults.", "You don’t need to consult anyone."]
    ]

    correct_templates = [
        "Benefits and risks vary by person; consult credible health sources.",
        "Evidence should come from organizations like WHO/CDC/NIH/MedlinePlus.",
        "Discuss with a healthcare professional, especially for teens or chronic conditions.",
        "Avoid treating it as a cure-all; monitor for side effects and interactions.",
        "Use guidance from credible sources before changing diet, supplements, or routines.",
        "Look for peer-reviewed studies or government health agencies.",
        "Health claims on social media are often exaggerated; confirm with experts.",
        "Trusted sources are better than personal anecdotes or viral trends.",
        "When in doubt, consult a licensed doctor or pharmacist.",
        "Safety and dosage can differ by age and health condition; tailor advice."
    ]

    ans_positions = _balanced_answer_positions(n)
    items = []
    for i in range(n):
        sub = random.choice(subthemes)
        stem = random.choice(stems).format(topic=topic, sub=sub)
        correct = random.choice(correct_templates)
        distractors = random.choice(distractor_buckets)[:3]
        choices = distractors[:]
        idx = ans_positions[i]
        choices.insert(idx, correct)
        items.append({
            "q": stem,
            "choices": choices,
            "answer_idx": idx,
            "explain": f"Credible guidance (e.g., WHO/CDC/NIH/MedlinePlus) cautions that '{topic}' is not a cure-all; weigh benefits/risks and seek professional advice when needed.",
            "source": "https://medlineplus.gov/",
            "topic": topic,  # <= per-item tag
        })
    return items


# ---- NEW: multi-topic helpers ----
def _topics_from_session(primary_topic: str | None, needed: int = 4) -> list[str]:
    """Pick a small set of topics to mix into a quiz."""
    pool = []
    if primary_topic:
        pool.append(primary_topic.strip())

    kw = (session.get("last_keywords") or "").strip()
    if kw and kw.lower() not in [t.lower() for t in pool]:
        pool.append(kw)

    misc = [
        "detox", "weight loss myths", "ozone therapy", "juice cleanse",
        "apple cider vinegar for fat loss", "cold plunge health claims",
        "vitamin megadosing", "spot reduction", "intermittent fasting for teens",
        "ketogenic diet for teens"
    ]
    for t in misc:
        if len(pool) >= needed:
            break
        if t.lower() not in [x.lower() for x in pool]:
            pool.append(t)
    return pool[:needed]
def multi_topic_fallback(topics: list[str], n: int = 10) -> list[dict]:
    """Build a mixed quiz drawing items from several topics."""
    if not topics:
        topics = ["general health"]
    items: list[dict] = []
    ti = 0
    while len(items) < n:
        t = topics[ti % len(topics)]
        batch = diversified_fallback(t, n=min(2, n - len(items)))  # items carry topic=t
        items.extend(batch)
        ti += 1
    items = ensure_unique_items(items, topic="__mixed__")
    random.shuffle(items)
    return items[:n]



def safe_get(url, headers=None, timeout=12, params=None):
    try:
        r = requests.get(url, headers=headers or COMMON_HEADERS, params=params, timeout=timeout)
        r.raise_for_status()
        return r
    except Exception:
        return None
def gpt_generate_mcqs(topic: str, n_questions: int = 10):
    if not (_OPENAI_AVAILABLE and os.getenv("OPENAI_API_KEY")):
        return []

    def _postprocess(items: list[dict]) -> list[dict]:
        # Validate + dedupe (keeps your safety around domains)
        valid = []
        for it in (items or []):
            if not isinstance(it, dict):
                continue
            q = (it.get("q") or "").strip()
            ch = it.get("choices") or []
            ai = it.get("answer_idx")
            src = (it.get("source") or "").strip()
            if (
                q and isinstance(ch, list) and len(ch) == 4
                and isinstance(ai, int) and 0 <= ai < 4
                and any(src.startswith(f"https://{d}") or src.startswith(f"http://{d}")
                        for d in ["who.int","cdc.gov","nih.gov","ncbi.nlm.nih.gov","medlineplus.gov"])
            ):
                valid.append({
                    "q": q,
                    "choices": [str(c).strip() for c in ch],
                    "answer_idx": int(ai),
                    "explain": (it.get("explain") or "").strip(),
                    "source": src,
                    "topic": (it.get("topic") or topic).strip(),
                })
        valid = ensure_unique_items(valid, topic)
        random.shuffle(valid)
        return valid[:n_questions]

    try:
        client = OpenAI(api_key=os.getenv("OPENAI_API_KEY"))

        sys_msg = (
            "You create safe, accurate multiple-choice questions (MCQs) for teens about health misinformation.\n"
            "Return STRICT JSON with key 'items' only. EXACTLY 10 items, no extra keys.\n"
            "Hard requirements:\n"
            "- Cover DIFFERENT subtopics; use at least 8 distinct subthemes from the provided list.\n"
            "- Each item: {q, choices[4], answer_idx (0..3), explain (1-2 sentences), source (WHO/CDC/NIH/MedlinePlus/NCBI)}.\n"
            "- Natural, varied wording (no templated stems). Avoid medical advice; stay neutral and evidence-based.\n"
            "- Distribute answer_idx positions across items (don’t always use the same index).\n"
            "- If an item narrows to a subtopic, include a 'topic' field per item.\n"
        )

        usr_payload = {
            "topic": topic,
            "n": n_questions,
            "subthemes": SUBTHEMES,
            "format": {
                "items": [{
                    "q": "string",
                    "choices": ["string","string","string","string"],
                    "answer_idx": 0,
                    "explain": "string",
                    "source": "https://(who.int|cdc.gov|nih.gov|medlineplus.gov|ncbi.nlm.nih.gov)/...",
                    "topic": "optional more-specific subtopic"
                }]
            }
        }

        resp = client.chat.completions.create(
            model=os.getenv("OPENAI_MODEL", "gpt-4o-mini"),
            temperature=0.2,
            response_format={"type": "json_object"},
            messages=[
                {"role": "system", "content": sys_msg},
                {
                    "role": "user",
                    "content": (
                        "Generate EXACTLY 10 MCQs covering at least 8 distinct subthemes from the list. "
                        "Use the topic below as the umbrella (it can be composite like 'term1, term2, term3'). "
                        "Return JSON with only the key 'items'.\n\n"
                        + json.dumps(usr_payload, ensure_ascii=False)
                    )
                },
            ],
            timeout=45
        )
        data = json.loads(resp.choices[0].message.content or "{}")
        return _postprocess(data.get("items", []))
    except Exception:
        return []


def oss_generate_mcqs(topic, contexts):
    try:
        from Questgen import main as qg
    except Exception:
        return []

    base_text = "\n\n".join(c["text"] for c in contexts)[:4000]
    if not base_text:
        return []

    try:
        qg_handler = qg.QGen()
        payload = {"input_text": base_text}
        output = qg_handler.predict_mcq(payload)
        items = []
        for m in output.get("questions", [])[:10]:
            stem = m.get("question")
            opts = m.get("options", [])[:4]
            ans  = m.get("answer")
            if stem and len(opts) == 4 and ans in opts:
                items.append({
                    "q": stem,
                    "choices": opts,
                    "answer_idx": opts.index(ans),
                    "explain": "Derived from trusted excerpts.",
                    "source": (contexts[0]["url"] if contexts else ""),
                    "topic": topic,  # <= tag with parent topic
                })
        return items
    except Exception:
        return []

# =========================
# Monitor-derived sources (optional)
# =========================
def get_trusted_sources_from_session_fallback(topic, max_urls=4):
    urls = []
    last = session.get("last_results")
    if last:
        for bucket in ("valid", "uncertain", "invalid"):
            for p in last.get(bucket, []):
                for c in (p.get("citations") or []):
                    u = c.get("url")
                    if u:
                        host = urlparse(u).hostname or ""
                        if any(host.endswith(dom) for dom in ALLOWED_HEALTH_DOMAINS):
                            urls.append(u)
                            if len(urls) >= max_urls:
                                break
            if len(urls) >= max_urls:
                break
    if not urls:
        urls = [
            f"https://medlineplus.gov/search/?query={requests.utils.quote(topic)}",
            "https://www.cdc.gov/healthyliving/index.htm",
        ]
    return list(dict.fromkeys(urls))[:max_urls]


# =========================
# Daily topic selection
# =========================
def pick_daily_topic():
    kw = (session.get("last_keywords") or "").strip()
    if kw:
        return kw
    fallback_topics = [
        "detox",
        "garlic weight loss",
        "ozone therapy",
        "juice cleanse",
        "apple cider vinegar for fat loss",
        "cold plunge health claims",
        "vitamin megadosing",
        "spot reduction",
        "intermittent fasting for teens",
        "ketogenic diet for teens",
    ]
    return fallback_topics[int(time.time()) % len(fallback_topics)]
def recent_search_terms(user_id: int | None, limit: int = 3) -> list[str]:
    """
    Return up to `limit` distinct, most-recent keywords the user searched for.
    Falls back to session['last_keywords'] if present and not already included.
    """
    terms: list[str] = []
    try:
        db = get_db()
        if user_id:
            rows = db.execute(
                """
                SELECT keywords
                FROM searches
                WHERE user_id = ?
                ORDER BY created_at DESC
                LIMIT 20
                """,
                (user_id,)
            ).fetchall()

            # collect unique terms in order
            seen = set()
            for r in rows:
                kw = (r["keywords"] or "").strip()
                if not kw:
                    continue
                # split on commas to allow multi-keyword saves, keep simple
                for part in [x.strip() for x in kw.split(",") if x.strip()]:
                    if part.lower() not in seen:
                        seen.add(part.lower())
                        terms.append(part)
                        if len(terms) >= limit:
                            break
                if len(terms) >= limit:
                    break

        # also consider the last_keywords in session as a final candidate
        session_kw = (session.get("last_keywords") or "").strip()
        if session_kw and all(session_kw.lower() != t.lower() for t in terms):
            terms.append(session_kw)

    except Exception:
        pass

    # keep at most limit and ensure uniqueness preserving order
    deduped = []
    seen_low = set()
    for t in terms:
        low = t.lower()
        if low not in seen_low:
            seen_low.add(low)
            deduped.append(t)
        if len(deduped) >= limit:
            break
    return deduped[:limit]


PRESET_TOPICS = [
    "detox",
    "garlic weight loss",
    "ozone therapy",
    "juice cleanse",
    "apple cider vinegar for fat loss",
    "cold plunge health claims",
    "vitamin megadosing",
    "spot reduction",
    "intermittent fasting for teens",
    "ketogenic diet for teens",
]

def composite_topic_for_today(user_id: int | None, max_terms: int = 3) -> tuple[str, list[str]]:
    """
    Compose a display topic like 'term1, term2, term3'.
    Also return the list of topics to mix for fallback generation.
    If no/too few recent terms, pad with PRESET_TOPICS.
    """
    recent = recent_search_terms(user_id, limit=max_terms)
    # pad if needed
    if len(recent) < max_terms:
        for p in PRESET_TOPICS:
            if len(recent) >= max_terms:
                break
            if all(p.lower() != t.lower() for t in recent):
                recent.append(p)
    display = ", ".join(recent[:max_terms]) if recent else PRESET_TOPICS[0]
    return display, recent[:max_terms]


# =========================
# Simple misinfo pattern fallback (for monitor)
# =========================
MISINFO_PATTERNS = [
    r"detox water|flush toxins|7[- ]day detox",
    r"raw garlic cures|cure[- ]?all|miracle cure",
    r"lose \d+\s?(kg|lbs) in \d+\s?(days?|weeks?)",
    r"spot reduction|melt fat",
    r"no side effects",
    r"ozone therapy cures",
]
MISINFO_RE = re.compile("|".join(MISINFO_PATTERNS), re.I)


# =========================
# YouTube & Reddit Fetchers
# =========================
def fetch_youtube_search(keyword, limit=10):
    key = os.getenv("YT_API_KEY")
    if key:
        data = _yt_api_search(keyword, key, limit)
        if data:
            return data
    if _FEEDPARSER_AVAILABLE:
        return _yt_rss_search(keyword, limit)
    return []

def _yt_api_search(keyword, key, limit):
    url = "https://www.googleapis.com/youtube/v3/search"
    params = {
        "part": "snippet",
        "q": keyword,
        "type": "video",
        "maxResults": min(limit, 50),
        "order": "date",
        "safeSearch": "moderate",
        "key": key,
    }
    try:
        r = requests.get(url, headers=COMMON_HEADERS, params=params, timeout=12)
        if r.status_code != 200:
            try:
                err = r.json()
            except Exception:
                err = r.text[:400]
            app.logger.warning("YouTube API %s for %r: %s", r.status_code, keyword, err)
            return []
        data = r.json()
    except Exception:
        app.logger.exception("YouTube API request crashed for %r", keyword)
        return []

    items = []
    for it in data.get("items", []):
        sn = it.get("snippet", {}) or {}
        vid = (it.get("id", {}) or {}).get("videoId")
        if not vid:
            continue
        published_at = sn.get("publishedAt")
        try:
            dt = datetime.fromisoformat((published_at or "").replace("Z", "+00:00"))
        except Exception:
            dt = now_utc()
        dt = to_aware_utc(dt)
        items.append({
            "platform": "YouTube",
            "author": (sn.get("channelTitle") or "YouTube").strip(),
            "text": f"{(sn.get('title') or '').strip()} — {(sn.get('description') or '').strip()}",
            "url": f"https://www.youtube.com/watch?v={vid}",
            "video_id": vid,
            "created_at": dt,
            "likes": None,
        })
        if len(items) >= limit:
            break
    if not items:
        app.logger.warning("YouTube API returned 0 items for %r (q=%s)", keyword, keyword)
    return items


def _yt_rss_search(keyword, limit):
    feed_url = f"https://www.youtube.com/feeds/videos.xml?search_query={requests.utils.quote(keyword)}"
    try:
        d = feedparser.parse(feed_url)
    except Exception:
        return []
    items = []
    for e in d.entries[:limit]:
        title = html.unescape(getattr(e, "title", "") or "")
        desc  = html.unescape(getattr(e, "summary", "") or "")
        link  = getattr(e, "link", None)
        author = getattr(e, "author", "YouTube")
        vid = _extract_yt_video_id(link)
        try:
            if getattr(e, "published_parsed", None):
                dt = datetime(*e.published_parsed[:6])
            else:
                dt = now_utc()
        except Exception:
            dt = now_utc()
        dt = to_aware_utc(dt)
        items.append({
            "platform": "YouTube",
            "author": author,
            "text": f"{title} — {desc}",
            "url": link,
            "video_id": vid,
            "created_at": dt,
            "likes": None
        })
    return items

def _extract_yt_video_id(link):
    if not link:
        return None
    try:
        qs = parse_qs(urlparse(link).query)
        if "v" in qs and qs["v"]:
            return qs["v"][0]
    except Exception:
        pass
    return None

def fetch_reddit_search(keyword, limit=10):
    url = "https://www.reddit.com/search.json"
    params = {"q": keyword, "sort": "new", "t": "week", "limit": min(limit, 25)}
    r = safe_get(url, headers=COMMON_HEADERS, params=params)
    if not r:
        return []
    try:
        data = r.json()
    except Exception:
        return []
    out = []
    for child in (data.get("data", {}).get("children", []) or []):
        d = child.get("data", {})
        text = d.get("title", "") or ""
        if d.get("selftext"):
            text += " — " + (d.get("selftext")[:300] or "")
        dt = datetime.utcfromtimestamp(d.get("created_utc", time.time()))
        dt = to_aware_utc(dt)
        out.append({
            "platform": "Reddit",
            "author": "u/" + (d.get("author") or "unknown"),
            "text": text.strip(),
            "url": "https://www.reddit.com" + (d.get("permalink") or ""),
            "video_id": None,
            "created_at": dt,
            "likes": d.get("ups"),
        })
        if len(out) >= limit:
            break
    return out


# =========================
# YouTube transcript helper
# =========================
def get_youtube_transcript(video_id, languages=("en", "en-US", "en-GB", "ko", "ko-KR"), max_chars=2000):
    if not _YT_TRANSCRIPT_AVAILABLE or not video_id:
        return None
    try:
        srt = YouTubeTranscriptApi.get_transcript(video_id, languages=list(languages))
        chunks = [seg.get("text", "") for seg in srt if seg.get("text")]
        text = " ".join(chunks).strip()
        if not text:
            return None
        return text[:max_chars]
    except (TranscriptsDisabled, NoTranscriptFound, VideoUnavailable):
        return None
    except Exception:
        return None


# =========================
# AI Validation (monitor)
# =========================
AI_SYSTEM = (
    "You are a health misinformation analyst for youth-focused social media. "
    "Given a short post, return strict JSON with keys: "
    "verdict (valid|invalid|uncertain), credibility_score (0..1), "
    "explanation (2-3 sentences), and citations (array of {title, url}). "
    "Prefer WHO, CDC, NIH, peer-reviewed sources."
)
def ensure_anon_id() -> str | None:
    """Create a stable anon token for this browser session (when user not logged in)."""
    if g.user:
        return None
    if not session.get("anon_id"):
        session["anon_id"] = secrets.token_hex(16)
    return session["anon_id"]
def create_quiz(topic: str, is_daily: bool, items: list[dict]) -> int:
    """Create a quiz and its items. Returns quiz_id."""
    db = get_db()
    cur = db.execute(
        "INSERT INTO quizzes (topic, is_daily, created_at) VALUES (?, ?, ?)",
        (topic, 1 if is_daily else 0, iso_now())
    )
    quiz_id = cur.lastrowid
    rows = []
    for i, it in enumerate(items):
        rows.append((
            quiz_id,
            i,
            it["q"],
            json.dumps(it["choices"], ensure_ascii=False),
            int(it["answer_idx"]),
            it.get("explain") or "",
            it.get("source") or "",
            (it.get("topic") or topic),   # <= per-item topic
        ))
    db.executemany(
        "INSERT INTO quiz_items (quiz_id, idx, q, choices, answer_idx, explain, source, topic) "
        "VALUES (?, ?, ?, ?, ?, ?, ?, ?)",
        rows
    )
    db.commit()
    return quiz_id


def get_daily_quiz_today_id() -> int | None:
    """Return today's daily quiz id if exists."""
    db = get_db()
    row = db.execute(
        "SELECT id FROM quizzes WHERE is_daily = 1 AND substr(created_at,1,10) = ? ORDER BY id DESC LIMIT 1",
        (today_str(),)
    ).fetchone()
    return row["id"] if row else None
def get_quiz_items_for_template(quiz_id: int) -> list[dict]:
    """Return items shaped for the Jinja template."""
    db = get_db()
    rows = db.execute(
        "SELECT id, idx, q, choices, answer_idx, explain, source, topic "
        "FROM quiz_items WHERE quiz_id = ? ORDER BY idx ASC",
        (quiz_id,)
    ).fetchall()
    items = []
    for r in rows:
        items.append({
            "id": r["id"],
            "q": r["q"],
            "choices": json.loads(r["choices"] or "[]"),
            "answer_idx": r["answer_idx"],
            "explain": r["explain"] or "",
            "source": r["source"] or "",
            "topic": r["topic"] or "",  # <= expose to Jinja
        })
    return items
def get_or_create_todays_daily(display_topic: str, mix_topics: list[str]) -> int:
    """
    Idempotently create today's daily quiz and ALWAYS save 10 items.
    """
    quiz_id = get_daily_quiz_today_id()
    if quiz_id:
        return quiz_id

    items = ensure_ten_mcqs(display_topic, mix_topics, target=10)
    return create_quiz(display_topic, is_daily=True, items=items)



def record_answer_and_score(quiz_id: int, attempt_id: int, item_idx: int, selected_idx: int):
    """
    First-attempt scoring:
      - +1 if the FIRST selection for this question is correct
      - +0 if the FIRST selection is wrong
      - Subsequent selections are ignored (no changes to stored answer or score)

    Returns: (correct: bool, answer_idx: int, new_score: int, explain: str, source: str)
    """
    db = get_db()

    # Locate the quiz item by index
    item = db.execute(
        "SELECT id, answer_idx, explain, source FROM quiz_items WHERE quiz_id = ? AND idx = ?",
        (quiz_id, item_idx)
    ).fetchone()
    if not item:
        return None, None, None, "", ""

    item_id = item["id"]
    correct_answer_idx = int(item["answer_idx"])

    # If already answered, ignore re-tries and return existing state + current score
    existing = db.execute(
        "SELECT selected_idx, correct FROM quiz_answers WHERE attempt_id = ? AND item_id = ?",
        (attempt_id, item_id)
    ).fetchone()
    if existing:
        cur_score = db.execute(
            "SELECT score FROM quiz_attempts WHERE id = ?",
            (attempt_id,)
        ).fetchone()["score"]
        return bool(existing["correct"]), correct_answer_idx, int(cur_score), (item["explain"] or ""), (item["source"] or "")

    # First attempt: record the selection
    is_correct = 1 if int(selected_idx) == correct_answer_idx else 0
    db.execute(
        """
        INSERT INTO quiz_answers (attempt_id, item_id, selected_idx, correct, answered_at)
        VALUES (?, ?, ?, ?, ?)
        """,
        (attempt_id, item_id, int(selected_idx), is_correct, iso_now())
    )

    # If correct on FIRST try, add +1 to score (wrong adds 0)
    if is_correct == 1:
        db.execute("UPDATE quiz_attempts SET score = score + 1 WHERE id = ?", (attempt_id,))

    db.commit()

    # Return updated score
    new_score = db.execute(
        "SELECT score FROM quiz_attempts WHERE id = ?",
        (attempt_id,)
    ).fetchone()["score"]

    return bool(is_correct), correct_answer_idx, int(new_score), (item["explain"] or ""), (item["source"] or "")


# =========================
# Routes
# =========================
@app.route("/")
def index():
    return render_template(
        "index.html",
        student="Jaein Kim",
        title="EPICHECK: AI-Driven Analysis of Youth Health Misinformation and Viral Trends"
    )

# ---------- Auth ----------
@app.route("/register", methods=["GET", "POST"])
def register():
    if g.user:
        return redirect(url_for("index"))

    error = None
    if request.method == "POST":
        name = (request.form.get("name") or "").strip()
        email = (request.form.get("email") or "").lower().strip()
        password = request.form.get("password") or ""
        confirm = request.form.get("confirm") or ""

        if not email or not password:
            error = "Email and password are required."
        elif len(password) < 8:
            error = "Password must be at least 8 characters."
        elif password != confirm:
            error = "Passwords do not match."
        elif get_user_by_email(email):
            error = "Email already registered."
        else:
            try:
                uid = create_user(name, email, password)
                session["user_id"] = uid
                return redirect(url_for("index"))
            except sqlite3.IntegrityError:
                error = "Email already registered."
            except Exception:
                error = "Registration failed. Try again."

    return render_template("register.html", error=error)

@app.route("/login", methods=["GET", "POST"])
def login():
    if g.user:
        return redirect(url_for("index"))

    error = None
    if request.method == "POST":
        email = (request.form.get("email") or "").lower().strip()
        password = request.form.get("password") or ""
        user = authenticate(email, password)
        if user:
            session["user_id"] = user["id"]
            next_url = request.args.get("next") or url_for("index")
            return redirect(next_url)
        error = "Invalid email or password."
    return render_template("login.html", error=error)

@app.route("/logout")
def logout():
    session.pop("user_id", None)
    return redirect(url_for("index"))

@app.route("/monitor", methods=["GET", "POST"])
@login_required
def monitor():
    keywords = (request.values.get("keywords") or "").strip()
    selected_sources = request.values.getlist("sources") or ["youtube", "reddit"]
    selected_sources = [s for s in selected_sources if s in ("youtube", "reddit")]

    results = {"valid": [], "invalid": [], "uncertain": []}
    sources_used = []

    if request.method == "POST" and keywords:
        try:
            # 1) Run search + AI validation
            results, sources_used = run_monitor_search(keywords, selected_sources)

            # 2) Persist search + posts for this logged-in user
            user_id = g.user["id"]
            search_id = save_monitor_search(
                keywords,
                sources_used or selected_sources,
                user_id
            )
            save_monitor_posts(search_id, results)

            # 3) Stash in session for quiz fallback, etc.
            session["last_results"] = results
            session["last_keywords"] = keywords
            session["last_search_id"] = search_id

        except Exception:
            app.logger.exception("Monitor search failed")
            flash("Search failed. Please try again in a moment.", "danger")

    return render_template(
        "monitor.html",
        keywords=keywords,
        results=results,
        sources_used=sources_used,
        now=iso_now(),
        selected_sources=selected_sources
    )
@app.get("/quiz/daily")
def quiz_daily():
    db = get_db()

    # Build composite topic and mix list (as you prefer – or keep your earlier function)
    display_topic, mix_topics = composite_topic_for_today(
        g.user["id"] if g.user else None, max_terms=3
    )

    quiz_id = get_daily_quiz_today_id()
    items = []
    points = 0
    progress = {}

    if quiz_id:
        session["active_quiz_id"] = quiz_id
        attempt = get_or_create_attempt(quiz_id)
        points = int(attempt["score"] or 0)
        items = get_quiz_items_for_template(quiz_id)
        progress = get_attempt_progress(quiz_id, attempt["id"])

        # keep original topic if present (so heading is stable)
        row = db.execute("SELECT topic FROM quizzes WHERE id = ?", (quiz_id,)).fetchone()
        if row and row["topic"]:
            display_topic = row["topic"]

    # If no items yet, template will show loader and JS will call /api/quiz/daily to create+hydrate.
    return render_template(
        "quiz.html",
        topic=display_topic,
        items=items,
        points=points,
        progress_json=json.dumps(progress)  # JS will use this to mark answered
    )




@app.route("/quiz/answer", methods=["POST"])
def quiz_answer():
    # AJAX endpoint from the quiz page
    try:
        payload = request.get_json(force=True)
        idx = int(payload.get("idx"))        # item index (0..9)
        choice = int(payload.get("choice"))  # selected option
    except Exception:
        return {"ok": False, "error": "Invalid payload"}, 400

    quiz_id = session.get("active_quiz_id")
    if not quiz_id:
        return {"ok": False, "error": "No active quiz"}, 400

    # Ensure attempt exists
    attempt = get_or_create_attempt(quiz_id)
    correct, answer_idx, new_score, explain, source = record_answer_and_score(
        quiz_id=quiz_id,
        attempt_id=attempt["id"],
        item_idx=idx,
        selected_idx=choice
    )
    if answer_idx is None:
        return {"ok": False, "error": "Invalid question index"}, 400

    return {
        "ok": True,
        "correct": bool(correct),
        "points": int(new_score),
        "explain": explain or "",
        "source": source or "",
        "answer_idx": int(answer_idx),
    }, 200


# =========================
# Simple history & API endpoints
# =========================
@app.route("/monitor/history")
def monitor_history():
    db = get_db()
    rows = db.execute(
        """
        SELECT s.id, s.keywords, s.sources, s.created_at, s.user_id,
               SUM(CASE WHEN p.verdict='valid' THEN 1 ELSE 0 END) AS valid_count,
               SUM(CASE WHEN p.verdict='invalid' THEN 1 ELSE 0 END) AS invalid_count,
               SUM(CASE WHEN p.verdict='uncertain' THEN 1 ELSE 0 END) AS uncertain_count
        FROM searches s
        LEFT JOIN posts p ON p.search_id = s.id
        GROUP BY s.id
        ORDER BY s.id DESC
        LIMIT 50
        """
    ).fetchall()
    return render_template("history.html", rows=rows)

@app.route("/api/monitor/searches")
def api_monitor_searches():
    db = get_db()
    rows = db.execute(
        "SELECT id, keywords, sources, created_at, user_id FROM searches ORDER BY id DESC LIMIT 100"
    ).fetchall()
    return jsonify([dict(r) for r in rows])

@app.route("/api/monitor/posts")
def api_monitor_posts():
    search_id = request.args.get("search_id", type=int)
    if not search_id:
        return jsonify({"error": "search_id required"}), 400
    db = get_db()
    rows = db.execute(
        """
        SELECT id, platform, author, text, url, video_id, created_at, verdict,
               credibility_score, explanation, likes, transcript_excerpt
        FROM posts WHERE search_id = ? ORDER BY id ASC
        """,
        (search_id,)
    ).fetchall()
    return jsonify([dict(r) for r in rows])
@app.route("/searches/<int:search_id>/delete", methods=["POST"])
@login_required
def delete_search(search_id: int):
    db = get_db()
    # Ensure the search belongs to the current user
    row = db.execute(
        "SELECT id FROM searches WHERE id = ? AND user_id = ?",
        (search_id, g.user["id"])
    ).fetchone()
    if not row:
        # not found or not owned by this user
        if request.is_json or request.headers.get("X-Requested-With") == "XMLHttpRequest":
            return jsonify({"ok": False, "error": "Not found"}), 404
        flash("Search not found.", "warning")
        return redirect(url_for("profile"))

    # Delete (posts will cascade)
    db.execute("DELETE FROM searches WHERE id = ? AND user_id = ?", (search_id, g.user["id"]))
    db.commit()

    if request.is_json or request.headers.get("X-Requested-With") == "XMLHttpRequest":
        return jsonify({"ok": True}), 200

    flash("Search deleted.", "success")
    return redirect(url_for("profile"))

def ai_validate(text_for_ai):
    api_key = os.getenv("OPENAI_API_KEY")
    if _OPENAI_AVAILABLE and api_key:
        try:
            client = OpenAI(api_key=api_key)
            resp = client.chat.completions.create(
                model=os.getenv("OPENAI_MODEL", "gpt-4o-mini"),
                temperature=0.2,
                messages=[
                    {"role": "system", "content": AI_SYSTEM},
                    {"role": "user", "content": f"Post:\n{text_for_ai}\nReturn JSON only."}
                ]
            )
            data = json.loads(resp.choices[0].message.content)
            data.setdefault("verdict", "uncertain")
            data.setdefault("credibility_score", 0.5)
            data.setdefault("explanation", "")
            data.setdefault("citations", [])
            return data
        except Exception:
            pass

    if MISINFO_RE.search(text_for_ai or ""):
        return {
            "verdict": "invalid",
            "credibility_score": 0.2,
            "explanation": "Matches common misinformation patterns (e.g., detox cures, miracle quick-weight-loss).",
            "citations": [
                {"title": "WHO Mythbusters", "url": "https://www.who.int"},
                {"title": "CDC Health Topics", "url": "https://www.cdc.gov"},
            ],
        }
    else:
        return {
            "verdict": "valid",
            "credibility_score": 0.7,
            "explanation": "No misinformation pattern detected in this brief text; still requires source verification.",
            "citations": [
                {"title": "MedlinePlus (Health Information)", "url": "https://medlineplus.gov/"},
            ],
        }

def run_monitor_search(keywords: str, selected_sources: list[str], limit_per_src: int = 10):
    """Fetch posts from selected sources, validate with AI, and bucket by verdict."""
    posts, sources_used = [], []

    # YouTube
    if "youtube" in selected_sources:
        yt_items = fetch_youtube_search(keywords, limit=min(limit_per_src, 12)) or []
        for it in yt_items:
            tx = get_youtube_transcript(it.get("video_id")) if it.get("video_id") else None
            if tx:
                it["transcript_excerpt"] = tx[:600]
            posts.append(it)
        if yt_items:
            sources_used.append("YouTube")

    # Reddit
    if "reddit" in selected_sources:
        rd_items = fetch_reddit_search(keywords, limit=min(limit_per_src, 12)) or []
        posts.extend(rd_items)
        if rd_items:
            sources_used.append("Reddit")

    if not posts:
        return {"valid": [], "invalid": [], "uncertain": []}, sources_used

    results = {"valid": [], "invalid": [], "uncertain": []}
    for p in posts:
        text_for_ai = (p.get("text") or "")
        if p.get("transcript_excerpt"):
            text_for_ai = f"{text_for_ai}\n\nTranscript: {p['transcript_excerpt']}"
        verdict = ai_validate(text_for_ai) or {}
        p["verdict"] = str(verdict.get("verdict", "uncertain")).lower()
        p["credibility_score"] = float(verdict.get("credibility_score", 0.5))
        p["explanation"] = verdict.get("explanation", "")
        p["citations"] = verdict.get("citations", []) or []
        bucket = p["verdict"] if p["verdict"] in results else "uncertain"
        results[bucket].append(p)

    return results, sources_used
@app.route("/profile")
@login_required
def profile():
    db = get_db()
    user_id = g.user["id"]

    attempts = db.execute(
        """
        SELECT
          qa.id            AS attempt_id,
          qa.quiz_id,
          qa.score,
          qa.started_at,
          qa.finished_at,
          q.topic,
          q.is_daily,
          (SELECT COUNT(*) FROM quiz_items WHERE quiz_id = qa.quiz_id) AS total_items,
          (SELECT COUNT(*) FROM quiz_answers WHERE attempt_id = qa.id) AS answered
        FROM quiz_attempts qa
        JOIN quizzes q ON q.id = qa.quiz_id
        WHERE qa.user_id = ?
        ORDER BY qa.started_at DESC
        LIMIT 10
        """,
        (user_id,)
    ).fetchall()

    stats = db.execute(
        """
        SELECT
          COUNT(*)                 AS total_quizzes,
          COALESCE(AVG(score), 0)  AS avg_score,
          COALESCE(MAX(score), 0)  AS best_score,
          MAX(started_at)          AS last_active
        FROM quiz_attempts
        WHERE user_id = ?
        """,
        (user_id,)
    ).fetchone() or {"total_quizzes": 0, "avg_score": 0, "best_score": 0, "last_active": None}

    searches = db.execute(
        """
        SELECT s.id, s.keywords, s.sources, s.created_at,
               SUM(CASE WHEN p.verdict='valid' THEN 1 ELSE 0 END)     AS valid_count,
               SUM(CASE WHEN p.verdict='invalid' THEN 1 ELSE 0 END)   AS invalid_count,
               SUM(CASE WHEN p.verdict='uncertain' THEN 1 ELSE 0 END) AS uncertain_count
        FROM searches s
        LEFT JOIN posts p ON p.search_id = s.id
        WHERE s.user_id = ?
        GROUP BY s.id
        ORDER BY s.id DESC
        LIMIT 10
        """,
        (user_id,)
    ).fetchall()

    per_topic = db.execute(
        """
        SELECT qi.topic,
               COUNT(*)            AS answered,
               SUM(qa.correct)     AS correct
        FROM quiz_answers qa
        JOIN quiz_items   qi ON qi.id   = qa.item_id
        JOIN quiz_attempts qatt ON qatt.id = qa.attempt_id
        WHERE qatt.user_id = ?
        GROUP BY qi.topic
        ORDER BY answered DESC
        LIMIT 20
        """,
        (user_id,)
    ).fetchall()

    return render_template(
        "profile.html",
        is_guest=False,
        user=g.user,
        stats=dict(stats),
        attempts=[dict(r) for r in attempts],
        searches=[dict(r) for r in searches],
        per_topic=[dict(r) for r in per_topic],  # <- pass to template if you want to render
    )

# ---------- Campaign helpers ----------
SLUG_ALPHABET = "abcdefghjkmnpqrstuvwxyz23456789"

def _slug(n=8):
    return "".join(random.choice(SLUG_ALPHABET) for _ in range(n))

def _unique_slug():
    db = get_db()
    for _ in range(8):
        s = _slug()
        row = db.execute("SELECT 1 FROM campaigns WHERE slug = ?", (s,)).fetchone()
        if not row:
            return s
    # extreme fallback: timestamped slug
    return _slug() + str(int(time.time()))

def _iso_date_utc(d: datetime) -> str:
    return d.astimezone(timezone.utc).date().isoformat()

def _first_monday_on_or_after(d: datetime) -> datetime:
    # align to next Monday for weekly cadence (club-friendly)
    wd = d.weekday()  # Mon=0
    return d if wd == 0 else d + timedelta(days=(7 - wd))

def _safe_sources_from_monitor(topic: str, max_urls=4):
    """Pull credible sources from session last_results or fallback to allowed domains."""
    urls = []
    last = session.get("last_results") or {}
    for bucket in ("valid", "uncertain", "invalid"):
        for p in last.get(bucket, []):
            for c in (p.get("citations") or []):
                u = (c.get("url") or "").strip()
                host = urlparse(u).hostname or ""
                if u and any(host.endswith(dom) for dom in ALLOWED_HEALTH_DOMAINS):
                    urls.append(u)
                    if len(urls) >= max_urls:
                        break
        if len(urls) >= max_urls:
            break
    if not urls:
        # generic fallbacks tied to topic
        urls = [
            f"https://medlineplus.gov/search/?query={requests.utils.quote(topic)}",
            "https://www.cdc.gov/healthyliving/index.htm",
            "https://www.nih.gov/health-information",
        ]
    # de-dupe while keeping order
    return list(dict.fromkeys(urls))[:max_urls]
from datetime import timedelta

def generate_weekly_plan(topic: str, audience: str, weeks: int = 4) -> list[dict]:
    """
    Poster-only plan.
    Each week gets one poster that teaches:
      - Common false knowledge (myths)
      - Evidence-based facts
      - How to check claims
      - Red flags to watch for
      - A small teen-specific note
    Stored as Markdown in `body` so templates can render immediately.
    """
    subs = [
        "common myths", "warning signs", "benefits vs. risks", "reliability of sources",
        "interactions/contraindications", "age-specific considerations", "dosage and limits",
        "online misinformation tactics", "overhyped benefits", "peer pressure and trends"
    ]

    is_school = (audience == "school_club")  # reserved for later copy tweaks
    sources = _safe_sources_from_monitor(topic)

    def poster_body_for_week(week_no: int, subtheme: str) -> str:
        # Tight, poster-ready sections. Keep it generic but useful for any topic.
        # Use short lines so it looks clean in the UI.
        return textwrap.dedent(f"""
        ## Poster — {topic.title()} ({subtheme.title()})

        ### Common False Knowledge
        1) “{topic} is **100% safe** for everyone.”
        2) “{topic} gives **instant results** with **no side effects**.”
        3) “If it’s **natural**, it’s **risk-free**.”
        4) “Anecdotes on social media **prove** it works.”

        ### What the Evidence Says
        - Benefits and risks vary by person and context.
        - Evidence should come from WHO / CDC / NIH / MedlinePlus or peer-reviewed studies.
        - Watch for interactions, contraindications, and age-specific guidance (teens ≠ adults).
        - No credible source promises guaranteed results.

        ### How to Check Claims (FAST)
        - **F**ind the author: gov/edu/WHO/CDC/NIH/MedlinePlus ≫ random blogs or influencers.
        - **A**sk for evidence: peer-reviewed or official guidance, not screenshots.
        - **S**can for red flags: “miracle”, “no side effects”, “detox toxins”.
        - **T**alk to a pro: pharmacist, clinician, or school nurse for teen-specific advice.

        ### Red Flags
        - “Cure-all”, “works for everyone”, “no risks”
        - Secret formulas or paywalled “protocols”
        - Cherry-picked testimonials, no methods or sample size
        - Appeals to popularity (“viral therefore true”)

        ### Teen Takeaway
        - Don’t copy adult dosages or routines.
        - If you have a condition, take meds, or play sports—**ask a professional first**.

        ### Credible Starting Points
        {chr(10).join(f"- {u}" for u in sources)}
        """).strip()

    plan = []
    for w in range(1, weeks + 1):
        sub = random.choice(subs)
        plan.append({
            "week_no": w,
            "content_type": "poster",
            "title": f"Week {w}: Poster — {topic.title()}",
            "body": poster_body_for_week(w, sub),
            "sources": sources,
        })
    return plan
@app.post("/api/quiz/generate")
def api_quiz_generate():
    data = request.get_json(force=True, silent=True) or {}
    topic = (data.get("topic") or "").strip()

    # Compose default composite topic if none provided
    if not topic:
        display_topic, mix_topics = composite_topic_for_today(
            g.user["id"] if g.user else None, max_terms=3
        )
        topic = display_topic
    else:
        mix_topics = [t.strip() for t in topic.split(",") if t.strip()]

    # 1) GPT on the (possibly composite) topic
    items = gpt_generate_mcqs(topic, n_questions=10)

    # 2) Retry GPT on the broader mix if short
    if len(items) < 10 and mix_topics:
        broader_topic = ", ".join(mix_topics) or topic
        more = gpt_generate_mcqs(broader_topic, n_questions=10)
        items = ensure_unique_items(items + more, topic="__mixed__")

    # 3) OSS fallback using trusted sources
    if len(items) < 10:
        contexts = fetch_trusted_pages(get_trusted_sources_from_session_fallback(topic))
        more = oss_generate_mcqs(topic, contexts) or []
        items = ensure_unique_items(items + more, topic="__mixed__")

    if len(items) < 10 and mix_topics:
        broader_topic = ", ".join(mix_topics) or topic
        contexts = fetch_trusted_pages(get_trusted_sources_from_session_fallback(broader_topic))
        more = oss_generate_mcqs(broader_topic, contexts) or []
        items = ensure_unique_items(items + more, topic="__mixed__")

    items = ensure_ten_mcqs(topic, mix_topics, target=10)

    quiz_id = create_quiz(topic, is_daily=False, items=items)
    session["active_quiz_id"] = quiz_id
    attempt = get_or_create_attempt(quiz_id)
    points = int(attempt["score"] or 0)
    items_out = get_quiz_items_for_template(quiz_id)

    return {"ok": True, "quiz_id": quiz_id, "points": points, "items": items_out}

def get_or_create_attempt(quiz_id: int):
    """Return attempt row (create if needed) for current user/anon."""
    db = get_db()
    if g.user:
        row = db.execute(
            "SELECT * FROM quiz_attempts WHERE quiz_id = ? AND user_id = ?",
            (quiz_id, g.user["id"])
        ).fetchone()
        if row:
            return row
        db.execute(
            "INSERT INTO quiz_attempts (quiz_id, user_id, started_at, score) VALUES (?, ?, ?, 0)",
            (quiz_id, g.user["id"], iso_now())
        )
    else:
        anon_id = ensure_anon_id()
        row = db.execute(
            "SELECT * FROM quiz_attempts WHERE quiz_id = ? AND anon_id = ?",
            (quiz_id, anon_id)
        ).fetchone()
        if row:
            return row
        db.execute(
            "INSERT INTO quiz_attempts (quiz_id, anon_id, started_at, score) VALUES (?, ?, ?, 0)",
            (quiz_id, anon_id, iso_now())
        )
    db.commit()
    return db.execute("SELECT * FROM quiz_attempts WHERE id = last_insert_rowid()").fetchone()

@app.post("/api/quiz/daily")
def api_quiz_daily():
    display_topic, mix_topics = composite_topic_for_today(
        g.user["id"] if g.user else None, max_terms=3
    )
    try:
        quiz_id = get_or_create_todays_daily(display_topic, mix_topics)
    except Exception as e:
        return {"ok": False, "error": str(e)}, 500

    session["active_quiz_id"] = quiz_id
    attempt = get_or_create_attempt(quiz_id)
    points = int(attempt["score"] or 0)
    items = get_quiz_items_for_template(quiz_id)
    progress = get_attempt_progress(quiz_id, attempt["id"])

    db = get_db()
    row = db.execute("SELECT topic FROM quizzes WHERE id = ?", (quiz_id,)).fetchone()
    final_topic = row["topic"] if row and row["topic"] else display_topic

    return {
        "ok": True,
        "quiz_id": quiz_id,
        "topic": final_topic,
        "points": points,
        "items": items,
        "progress": progress,
    }



def persist_campaign(user_id: int, title: str, topic: str, audience: str, visibility: str, starts_on: str, weeks: int, plan: list[dict]) -> int:
    db = get_db()
    slug = _unique_slug()
    db.execute(
        "INSERT INTO campaigns (user_id, title, topic, audience, visibility, starts_on, weeks, created_at, slug) "
        "VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)",
        (user_id, title, topic, audience, visibility, starts_on, weeks, iso_now(), slug)
    )
    cid = db.execute("SELECT last_insert_rowid()").fetchone()[0]

    rows = []
    for item in plan:
        rows.append((
            cid,
            int(item["week_no"]),
            item["content_type"],
            item["title"],
            item["body"],
            json.dumps(item.get("sources") or [], ensure_ascii=False),
            iso_now()
        ))
    db.executemany(
        "INSERT INTO campaign_items (campaign_id, week_no, content_type, title, body, sources, created_at) "
        "VALUES (?, ?, ?, ?, ?, ?, ?)",
        rows
    )
    db.commit()
    return cid
# ---------- Campaign routes ----------
from datetime import date

@app.route("/campaigns")
@login_required
def campaigns_index():
    db = get_db()
    rows = db.execute(
        "SELECT id, title, topic, audience, visibility, starts_on, weeks, slug, created_at "
        "FROM campaigns WHERE user_id = ? ORDER BY id DESC",
        (g.user["id"],)
    ).fetchall()
    return render_template("campaigns/index.html", rows=[dict(r) for r in rows])

@app.route("/campaigns/new", methods=["GET", "POST"])
@login_required
def campaigns_new():
    error = None
    if request.method == "POST":
        title = (request.form.get("title") or "").strip()
        topic = (request.form.get("topic") or "").strip()
        audience = (request.form.get("audience") or "school_club").strip()
        visibility = (request.form.get("visibility") or "public").strip()
        weeks = int(request.form.get("weeks") or 4)
        starts_on = (request.form.get("starts_on") or "").strip()

        if not title or not topic:
            error = "Title and topic are required."
        else:
            # default start: next Monday in APP_TZ
            if not starts_on:
                now_local = datetime.now(ZoneInfo(APP_TZ))
                starts_on = _iso_date_utc(_first_monday_on_or_after(now_local))
            try:
                plan = generate_weekly_plan(topic=topic, audience=audience, weeks=weeks)
                cid = persist_campaign(
                    user_id=g.user["id"],
                    title=title,
                    topic=topic,
                    audience=audience,
                    visibility=visibility,
                    starts_on=starts_on,
                    weeks=weeks,
                    plan=plan
                )
                return redirect(url_for("campaigns_view", campaign_id=cid))
            except Exception:
                app.logger.exception("Failed to create campaign")
                error = "Failed to create campaign. Please try again."

    # GET: render form
    return render_template("campaigns/new.html", error=error, today=date.today().isoformat())

@app.route("/campaigns/<int:campaign_id>")
@login_required
def campaigns_view(campaign_id: int):
    db = get_db()
    camp = db.execute(
        "SELECT * FROM campaigns WHERE id = ? AND user_id = ?",
        (campaign_id, g.user["id"])
    ).fetchone()
    if not camp:
        flash("Campaign not found.", "warning")
        return redirect(url_for("campaigns_index"))

    items = db.execute(
        "SELECT week_no, content_type, title, body, sources, created_at "
        "FROM campaign_items WHERE campaign_id = ? ORDER BY week_no, id",
        (campaign_id,)
    ).fetchall()

    # Group by week
    by_week = {}
    for r in items:
        wk = int(r["week_no"])
        by_week.setdefault(wk, []).append({
            "content_type": r["content_type"],
            "title": r["title"],
            "body": r["body"],
            "sources": json.loads(r["sources"] or "[]"),
            "created_at": r["created_at"],
        })

    return render_template("campaigns/view.html", campaign=dict(camp), weeks=by_week)

@app.route("/c/<slug>")
def campaigns_public(slug: str):
    """Public read-only page for sharing."""
    db = get_db()
    camp = db.execute(
        "SELECT * FROM campaigns WHERE slug = ?",
        (slug,)
    ).fetchone()
    if not camp:
        flash("Campaign not found.", "warning")
        return redirect(url_for("index"))
    if camp["visibility"] != "public":
        flash("This campaign is private.", "warning")
        return redirect(url_for("index"))

    items = db.execute(
        "SELECT week_no, content_type, title, body, sources "
        "FROM campaign_items WHERE campaign_id = ? ORDER BY week_no, id",
        (camp["id"],)
    ).fetchall()

    by_week = {}
    for r in items:
        wk = int(r["week_no"])
        by_week.setdefault(wk, []).append({
            "content_type": r["content_type"],
            "title": r["title"],
            "body": r["body"],
            "sources": json.loads(r["sources"] or "[]"),
        })

    return render_template("campaigns/public.html", campaign=dict(camp), weeks=by_week)


# =========================
# Main
# =========================
if __name__ == "__main__":
    # Never hardcode API keys; set OPENAI_API_KEY and YT_API_KEY in your environment
    app.run(debug=True)
