# app.py — single-file EPICHECK + Poster Studio

import os, re, time, html, json, textwrap, sqlite3, base64, uuid, secrets, random, string
from datetime import datetime, timezone, timedelta, date
from urllib.parse import urlparse, parse_qs

import requests
from flask import (
    Flask, Blueprint, render_template, request, session, redirect,
    url_for, g, jsonify, flash, abort
)
from dotenv import load_dotenv
from bs4 import BeautifulSoup
from werkzeug.security import generate_password_hash, check_password_hash
from functools import wraps
from zoneinfo import ZoneInfo

# ========= Config =========
APP_TZ = os.getenv("APP_TZ", "Asia/Seoul")
load_dotenv()
app = Flask(__name__)
app.secret_key = os.getenv("SECRET_KEY", "dev-secret-key-change-me")
COMMON_HEADERS = {"User-Agent": "EPICHECK/1.0 (+https://example.edu)"}
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

# Optional deps
try:
    from openai import OpenAI
    _OPENAI_AVAILABLE = True
except Exception:
    _OPENAI_AVAILABLE = False

try:
    import feedparser
    _FEEDPARSER_AVAILABLE = True
except Exception:
    _FEEDPARSER_AVAILABLE = False

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


# ========= Time helpers =========
def _parse_iso_any(value):
    """Best-effort parse of ISO-ish strings to aware UTC datetime."""
    if isinstance(value, datetime):
        dt = value
    else:
        s = str(value or "").strip()
        try:
            dt = datetime.fromisoformat(s.replace("Z", "+00:00"))
        except Exception:
            try:
                dt = datetime.strptime(s, "%Y-%m-%d %H:%M:%S")
            except Exception:
                return None
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
        local = dt
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


# ========= DB helpers =========
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

        -- Users / Monitoring
        CREATE TABLE IF NOT EXISTS users (
            id            INTEGER PRIMARY KEY AUTOINCREMENT,
            name          TEXT,
            email         TEXT NOT NULL UNIQUE,
            password_hash TEXT NOT NULL,
            created_at    TEXT NOT NULL
        );
        CREATE INDEX IF NOT EXISTS idx_users_email ON users(email);

        CREATE TABLE IF NOT EXISTS searches (
            id          INTEGER PRIMARY KEY AUTOINCREMENT,
            keywords    TEXT NOT NULL,
            sources     TEXT NOT NULL,
            created_at  TEXT NOT NULL,
            user_id     INTEGER,
            FOREIGN KEY (user_id) REFERENCES users(id) ON DELETE SET NULL
        );
        CREATE INDEX IF NOT EXISTS idx_searches_created_at ON searches(created_at);

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
        CREATE INDEX IF NOT EXISTS idx_posts_search_id ON posts(search_id);

        -- Quizzes
        CREATE TABLE IF NOT EXISTS quizzes (
            id         INTEGER PRIMARY KEY AUTOINCREMENT,
            topic      TEXT NOT NULL,
            is_daily   INTEGER NOT NULL DEFAULT 0,
            created_at TEXT NOT NULL
        );
        CREATE TABLE IF NOT EXISTS quiz_items (
            id         INTEGER PRIMARY KEY AUTOINCREMENT,
            quiz_id    INTEGER NOT NULL,
            idx        INTEGER NOT NULL,
            q          TEXT NOT NULL,
            choices    TEXT NOT NULL,
            answer_idx INTEGER NOT NULL,
            explain    TEXT,
            source     TEXT,
            topic      TEXT,
            FOREIGN KEY (quiz_id) REFERENCES quizzes(id) ON DELETE CASCADE
        );
        CREATE INDEX IF NOT EXISTS idx_quiz_items_quiz ON quiz_items(quiz_id);

        CREATE TABLE IF NOT EXISTS quiz_attempts (
            id         INTEGER PRIMARY KEY AUTOINCREMENT,
            quiz_id    INTEGER NOT NULL,
            user_id    INTEGER,
            anon_id    TEXT,
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

        -- Legacy Campaigns (keep if still used)
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

        -- NEW: Poster Studio tables
        CREATE TABLE IF NOT EXISTS poster_campaigns (
            id         INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id    INTEGER NOT NULL,
            title      TEXT NOT NULL,
            topic      TEXT NOT NULL,
            audience   TEXT NOT NULL,  -- 'school_club' | 'public'
            visibility TEXT NOT NULL,  -- 'private' | 'public'
            starts_on  TEXT NOT NULL,
            weeks      INTEGER NOT NULL DEFAULT 4,
            slug       TEXT NOT NULL UNIQUE,
            created_at TEXT NOT NULL,
            FOREIGN KEY (user_id) REFERENCES users(id) ON DELETE CASCADE
        );
        CREATE TABLE IF NOT EXISTS posters (
            id           INTEGER PRIMARY KEY AUTOINCREMENT,
            campaign_id  INTEGER NOT NULL,
            week_no      INTEGER NOT NULL,
            prompt       TEXT NOT NULL,
            img_path     TEXT NOT NULL,
            seed         TEXT,
            width        INTEGER NOT NULL,
            height       INTEGER NOT NULL,
            created_at   TEXT NOT NULL,
            FOREIGN KEY (campaign_id) REFERENCES poster_campaigns(id) ON DELETE CASCADE
        );
        """
    )

    # Lightweight migrations/backfills
    if not _col_exists(db, "searches", "user_id"):
        db.execute("ALTER TABLE searches ADD COLUMN user_id INTEGER")

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

    # Ensure campaign slug index exists for legacy table
    try:
        db.execute("CREATE UNIQUE INDEX IF NOT EXISTS uq_campaigns_slug ON campaigns(slug)")
    except Exception:
        pass

    db.commit()

with app.app_context():
    init_db()


# ========= Auth & User =========
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


# ========= Monitor persistence =========
def save_monitor_search(keywords: str, sources_used: list[str], user_id: int | None) -> int:
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


# ========= Utilities =========
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
    s = (s or "").lower()
    s = s.replace("’", "'").replace("“", '"').replace("”", '"')
    s = re.sub(r"\s+", " ", s)
    s = s.translate(str.maketrans("", "", string.punctuation))
    return s.strip()

def ensure_unique_items(items: list[dict], topic: str) -> list[dict]:
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
            "answer_idx": int(r["answer_idx"]),
        }
    return out


# ========= Quiz generation helpers =========
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
            "- Distribute answer_idx positions across items.\n"
            "- If an item narrows to a subtopic, include a 'topic' field per item.\n"
        )
        usr_payload = {"topic": topic, "n": n_questions, "subthemes": SUBTHEMES}
        resp = client.chat.completions.create(
            model=os.getenv("OPENAI_MODEL", "gpt-4o-mini"),
            temperature=0.2,
            response_format={"type": "json_object"},
            messages=[
                {"role": "system", "content": sys_msg},
                {"role": "user", "content": "Generate EXACTLY 10 MCQs. Return JSON with only key 'items'.\n" + json.dumps(usr_payload, ensure_ascii=False)},
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
                    "topic": topic,
                })
        return items
    except Exception:
        return []

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

def recent_search_terms(user_id: int | None, limit: int = 3) -> list[str]:
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
            seen = set()
            for r in rows:
                kw = (r["keywords"] or "").strip()
                if not kw:
                    continue
                for part in [x.strip() for x in kw.split(",") if x.strip()]:
                    if part.lower() not in seen:
                        seen.add(part.lower())
                        terms.append(part)
                        if len(terms) >= limit:
                            break
                if len(terms) >= limit:
                    break
        session_kw = (session.get("last_keywords") or "").strip()
        if session_kw and all(session_kw.lower() != t.lower() for t in terms):
            terms.append(session_kw)
    except Exception:
        pass
    deduped, seen_low = [], set()
    for t in terms:
        low = t.lower()
        if low not in seen_low:
            seen_low.add(low)
            deduped.append(t)
        if len(deduped) >= limit:
            break
    return deduped[:limit]

def composite_topic_for_today(user_id: int | None, max_terms: int = 3) -> tuple[str, list[str]]:
    recent = recent_search_terms(user_id, limit=max_terms)
    if len(recent) < max_terms:
        for p in PRESET_TOPICS:
            if len(recent) >= max_terms:
                break
            if all(p.lower() != t.lower() for t in recent):
                recent.append(p)
    display = ", ".join(recent[:max_terms]) if recent else PRESET_TOPICS[0]
    return display, recent[:max_terms]

def _balanced_answer_positions(n: int) -> list[int]:
    base = [0,1,2,3] * ((n+3)//4)
    random.shuffle(base)
    return base[:n]

def diversified_fallback(topic: str, n: int = 10) -> list[dict]:
    subthemes = SUBTHEMES[:]
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
            "topic": topic,
        })
    return items

def ensure_ten_mcqs(display_topic: str, mix_topics: list[str], target: int = 10) -> list[dict]:
    items: list[dict] = []
    items.extend(gpt_generate_mcqs(display_topic, n_questions=target))
    if len(items) < target and mix_topics:
        broader_topic = ", ".join([t for t in mix_topics if t]) or display_topic
        more = gpt_generate_mcqs(broader_topic, n_questions=target)
        items = ensure_unique_items(items + more, topic="__mixed__")
    if len(items) < target:
        ctx = fetch_trusted_pages(get_trusted_sources_from_session_fallback(display_topic))
        more = oss_generate_mcqs(display_topic, ctx) or []
        items = ensure_unique_items(items + more, topic="__mixed__")
    if len(items) < target and mix_topics:
        broader_topic = ", ".join([t for t in mix_topics if t]) or display_topic
        ctx = fetch_trusted_pages(get_trusted_sources_from_session_fallback(broader_topic))
        more = oss_generate_mcqs(broader_topic, ctx) or []
        items = ensure_unique_items(items + more, topic="__mixed__")
    if len(items) < target:
        topics_pool = [t for t in (mix_topics or []) if t] + [t for t in PRESET_TOPICS]
        i = 0
        while len(items) < target:
            topic = topics_pool[i % len(topics_pool)]
            need = target - len(items)
            batch = diversified_fallback(topic, n=min(3, need))
            items = ensure_unique_items(items + batch, topic="__mixed__")
            i += 1
    random.shuffle(items)
    return items[:target]


# ========= Poster generator =========
POSTER_DIR = os.path.join(os.path.dirname(__file__), "static", "posters")
os.makedirs(POSTER_DIR, exist_ok=True)

def poster_prompt(topic: str, subtheme: str, audience: str) -> str:
    return f"""
Design a clean, evidence-based educational poster about "{topic}" focused on "{subtheme}" for teens ({audience}).
Style: modern school health poster, minimal icons, big headline, legible body, subtle accent shapes.
Avoid medical advice; avoid logos; no small text blocks. Include short checklist/flags area.
Color palette: cool neutrals + one accent. No brand text.
"""

def generate_poster_png(topic: str, subtheme: str, audience: str, seed: str | None = None,
                        width=1024, height=1536) -> tuple[str, str]:
    """
    Returns (absolute_file_path, file_basename). Requires OPENAI_API_KEY.
    """
    client = OpenAI(api_key=os.getenv("OPENAI_API_KEY"))
    prompt = poster_prompt(topic, subtheme, audience)
    resp = client.images.generate(
        model=os.getenv("OPENAI_IMAGE_MODEL", "gpt-image-1"),
        prompt=prompt.strip(),
        size=f"{width}x{height}",
        n=1,
    )
    b64 = resp.data[0].b64_json
    raw = base64.b64decode(b64)
    name = f"poster_{uuid.uuid4().hex}.png"
    out_path = os.path.join(POSTER_DIR, name)
    with open(out_path, "wb") as f:
        f.write(raw)
    return out_path, name


# ========= Studio blueprint =========

SLUG_ALPH = "abcdefghjkmnpqrstuvwxyz23456789"
def _slug(n=8):
    return "".join(secrets.choice(SLUG_ALPH) for _ in range(n))

def _unique_slug(db):
    for _ in range(12):
        s = _slug()
        r = db.execute("SELECT 1 FROM poster_campaigns WHERE slug=?", (s,)).fetchone()
        if not r:
            return s
    return _slug(10)

def _first_monday_on_or_after(d: datetime) -> datetime:
    wd = d.weekday()
    return d if wd == 0 else d + timedelta(days=(7 - wd))

@app.route("/studio")
@login_required
def studio_home():
    if not g.user:
        return redirect(url_for("login", next=request.path))
    db = get_db()
    rows = db.execute(
        "SELECT id, title, topic, audience, visibility, slug, starts_on, weeks, created_at "
        "FROM poster_campaigns WHERE user_id=? ORDER BY id DESC",
        (g.user["id"],)
    ).fetchall()
    return render_template("studio/index.html", rows=[dict(r) for r in rows])

@app.route("/studio/new", methods=["GET","POST"])
@login_required
def studio_new():
    if not g.user:
        return redirect(url_for("login", next=request.path))
    error = None
    if request.method == "POST":
        title     = (request.form.get("title") or "").strip()
        topic     = (request.form.get("topic") or "").strip()
        audience  = (request.form.get("audience") or "school_club").strip()
        visibility= (request.form.get("visibility") or "public").strip()
        weeks     = int(request.form.get("weeks") or 4)
        starts_on = (request.form.get("starts_on") or "").strip()
        if not title or not topic:
            error = "Title and topic are required."
        else:
            if not starts_on:
                now_local = datetime.now(ZoneInfo(APP_TZ))
                starts_on = _first_monday_on_or_after(now_local).astimezone(timezone.utc).date().isoformat()
            try:
                db = get_db()
                slug = _unique_slug(db)
                db.execute(
                    "INSERT INTO poster_campaigns (user_id,title,topic,audience,visibility,starts_on,weeks,slug,created_at) "
                    "VALUES (?,?,?,?,?,?,?,?,?)",
                    (g.user["id"], title, topic, audience, visibility, starts_on, weeks, slug, iso_now())
                )
                db.commit()
                cid = db.execute("SELECT last_insert_rowid()").fetchone()[0]
                return redirect(url_for("studio.studio_view", campaign_id=cid))
            except Exception:
                error = "Failed to create."
    return render_template("studio/new.html", error=error)

@app.route("/studio/c/<int:campaign_id>")
@login_required
def studio_view(campaign_id: int):
    if not g.user:
        return redirect(url_for("login", next=request.path))
    db = get_db()
    camp = db.execute(
        "SELECT * FROM poster_campaigns WHERE id=? AND user_id=?",
        (campaign_id, g.user["id"])
    ).fetchone()
    if not camp:
        flash("Not found", "warning")
        return redirect(url_for("studio.studio_home"))
    posters = db.execute(
        "SELECT * FROM posters WHERE campaign_id=? ORDER BY week_no",
        (campaign_id,)
    ).fetchall()
    return render_template("studio/view.html", campaign=dict(camp), posters=[dict(p) for p in posters])

@app.route("/studio/generate", methods=["POST"])
@login_required
def studio_generate():
    # if not g.user:
    #     abort(403)
    print("Called A")
    db = get_db()
    campaign_id = int(request.form.get("campaign_id") or 0)
    week_no     = int(request.form.get("week_no") or 1)
    subtheme    = (request.form.get("subtheme") or "common myths").strip()
    seed        = (request.form.get("seed") or "").strip() or None
    w           = int(request.form.get("w") or 1024)
    h           = int(request.form.get("h") or 1536)
    print("Called B")
    camp = db.execute(
        "SELECT id, topic, audience FROM poster_campaigns WHERE id=? AND user_id=?",
        (campaign_id, g.user["id"])
    ).fetchone()
    print("Called C")

    abs_path, name = generate_poster_png(
        topic=camp["topic"], subtheme=subtheme, audience=camp["audience"],
        seed=seed, width=w, height=h
    )
    print("Called D")
    rel_path = f"static/posters/{name}"
    prompt_used = f"{camp['topic']} — {subtheme} — {camp['audience']}"
    db.execute(
        "INSERT INTO posters (campaign_id, week_no, prompt, img_path, seed, width, height, created_at) "
        "VALUES (?,?,?,?,?,?,?,?)",
        (campaign_id, week_no, prompt_used, rel_path, seed, w, h, iso_now())
    )
    print("Called E")
    db.commit()
    return redirect(url_for("studio.studio_view", campaign_id=campaign_id))

# Fetch a plain-text transcript for a YouTube video (best-effort, safe fallback)
def get_youtube_transcript(video_id: str, max_chars: int = 4000) -> str | None:
    """
    Returns a concatenated transcript string if available, otherwise None.
    Respects the optional youtube_transcript_api dependency and handles common errors.
    """
    if not (_YT_TRANSCRIPT_AVAILABLE and video_id):
        return None

    try:
        # Try English first, then auto-generated/other languages (tweak as needed)
        transcript_list = YouTubeTranscriptApi.list_transcripts(video_id)

        preferred = None
        # Prefer a manually-created English transcript if present
        for lang in ("en", "en-US", "en-GB"):
            if transcript_list.find_transcript([lang]).is_generated is False:
                preferred = transcript_list.find_transcript([lang])
                break

        # Otherwise accept an English auto-generated transcript
        if preferred is None:
            for lang in ("en", "en-US", "en-GB"):
                try:
                    t = transcript_list.find_transcript([lang])
                    preferred = t  # may be auto-generated
                    break
                except Exception:
                    pass

        # As a final fallback, just pick the first transcript available
        if preferred is None:
            try:
                preferred = next(iter(transcript_list))
            except StopIteration:
                return None

        chunks = preferred.fetch()
        text = " ".join((c.get("text") or "").replace("\n", " ").strip() for c in chunks if c.get("text"))
        text = " ".join(text.split())[:max_chars]
        return text or None

    except (TranscriptsDisabled, NoTranscriptFound, VideoUnavailable):
        return None
    except Exception:
        return None


@app.route("/p/<slug>")
def studio_public(slug: str):
    db = get_db()
    camp = db.execute("SELECT * FROM poster_campaigns WHERE slug=?", (slug,)).fetchone()
    if not camp:
        abort(404)
    if camp["visibility"] != "public":
        flash("This campaign is private.", "warning")
        return redirect(url_for("index"))
    posters = db.execute(
        "SELECT week_no, img_path FROM posters WHERE campaign_id=? ORDER BY week_no",
        (camp["id"],)
    ).fetchall()
    return render_template("studio/public.html",
                           campaign=dict(camp),
                           posters=[dict(p) for p in posters])



# ========= Monitoring (YouTube/Reddit) =========
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
            return []
        data = r.json()
    except Exception:
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


# ========= AI Validation =========
AI_SYSTEM = (
    "You are a health misinformation analyst for youth-focused social media. "
    "Given a short post, return strict JSON with keys: "
    "verdict (valid|invalid|uncertain), credibility_score (0..1), "
    "explanation (2-3 sentences), and citations (array of {title, url}). "
    "Prefer WHO, CDC, NIH, peer-reviewed sources."
)

def ensure_anon_id() -> str | None:
    if g.user:
        return None
    if not session.get("anon_id"):
        session["anon_id"] = secrets.token_hex(16)
    return session["anon_id"]

def create_quiz(topic: str, is_daily: bool, items: list[dict]) -> int:
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
            (it.get("topic") or topic),
        ))
    db.executemany(
        "INSERT INTO quiz_items (quiz_id, idx, q, choices, answer_idx, explain, source, topic) "
        "VALUES (?, ?, ?, ?, ?, ?, ?, ?)",
        rows
    )
    db.commit()
    return quiz_id

def get_daily_quiz_today_id() -> int | None:
    db = get_db()
    row = db.execute(
        "SELECT id FROM quizzes WHERE is_daily = 1 AND substr(created_at,1,10) = ? ORDER BY id DESC LIMIT 1",
        (today_str(),)
    ).fetchone()
    return row["id"] if row else None

def get_quiz_items_for_template(quiz_id: int) -> list[dict]:
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
            "topic": r["topic"] or "",
        })
    return items

def get_or_create_todays_daily(display_topic: str, mix_topics: list[str]) -> int:
    quiz_id = get_daily_quiz_today_id()
    if quiz_id:
        return quiz_id
    items = ensure_ten_mcqs(display_topic, mix_topics, target=10)
    return create_quiz(display_topic, is_daily=True, items=items)

def record_answer_and_score(quiz_id: int, attempt_id: int, item_idx: int, selected_idx: int):
    db = get_db()
    item = db.execute(
        "SELECT id, answer_idx, explain, source FROM quiz_items WHERE quiz_id = ? AND idx = ?",
        (quiz_id, item_idx)
    ).fetchone()
    if not item:
        return None, None, None, "", ""
    item_id = item["id"]
    correct_answer_idx = int(item["answer_idx"])
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
    is_correct = 1 if int(selected_idx) == correct_answer_idx else 0
    db.execute(
        """
        INSERT INTO quiz_answers (attempt_id, item_id, selected_idx, correct, answered_at)
        VALUES (?, ?, ?, ?, ?)
        """,
        (attempt_id, item_id, int(selected_idx), is_correct, iso_now())
    )
    if is_correct == 1:
        db.execute("UPDATE quiz_attempts SET score = score + 1 WHERE id = ?", (attempt_id,))
    db.commit()
    new_score = db.execute(
        "SELECT score FROM quiz_attempts WHERE id = ?",
        (attempt_id,)
    ).fetchone()["score"]
    return bool(is_correct), correct_answer_idx, int(new_score), (item["explain"] or ""), (item["source"] or "")


# ========= Routes =========
@app.route("/")
def index():
    return render_template(
        "index.html",
        student="Jaein Kim",
        title="EPICHECK: AI-Driven Analysis of Youth Health Misinformation and Viral Trends"
    )

# Auth
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

# Monitor
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
            results, sources_used = run_monitor_search(keywords, selected_sources)
            user_id = g.user["id"]
            search_id = save_monitor_search(
                keywords,
                sources_used or selected_sources,
                user_id
            )
            save_monitor_posts(search_id, results)
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

# Quiz
@app.get("/quiz/daily")
@login_required
def quiz_daily():
    db = get_db()
    display_topic, mix_topics = composite_topic_for_today(
        g.user["id"] if g.user else None, max_terms=3
    )
    quiz_id = get_daily_quiz_today_id()
    items, points, progress = [], 0, {}
    if quiz_id:
        session["active_quiz_id"] = quiz_id
        attempt = get_or_create_attempt(quiz_id)
        points = int(attempt["score"] or 0)
        items = get_quiz_items_for_template(quiz_id)
        progress = get_attempt_progress(quiz_id, attempt["id"])
        row = db.execute("SELECT topic FROM quizzes WHERE id = ?", (quiz_id,)).fetchone()
        if row and row["topic"]:
            display_topic = row["topic"]
    return render_template(
        "quiz.html",
        topic=display_topic,
        items=items,
        points=points,
        progress_json=json.dumps(progress)
    )

@app.route("/quiz/answer", methods=["POST"])
def quiz_answer():
    try:
        payload = request.get_json(force=True)
        idx = int(payload.get("idx"))
        choice = int(payload.get("choice"))
    except Exception:
        return {"ok": False, "error": "Invalid payload"}, 400
    quiz_id = session.get("active_quiz_id")
    if not quiz_id:
        return {"ok": False, "error": "No active quiz"}, 400
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
    row = db.execute(
        "SELECT id FROM searches WHERE id = ? AND user_id = ?",
        (search_id, g.user["id"])
    ).fetchone()
    if not row:
        if request.is_json or request.headers.get("X-Requested-With") == "XMLHttpRequest":
            return jsonify({"ok": False, "error": "Not found"}), 404
        flash("Search not found.", "warning")
        return redirect(url_for("profile"))
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
    MISINFO_PATTERNS = [
        r"detox water|flush toxins|7[- ]day detox",
        r"raw garlic cures|cure[- ]?all|miracle cure",
        r"lose \d+\s?(kg|lbs) in \d+\s?(days?|weeks?)",
        r"spot reduction|melt fat",
        r"no side effects",
        r"ozone therapy cures",
    ]
    MISINFO_RE = re.compile("|".join(MISINFO_PATTERNS), re.I)
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
    posts, sources_used = [], []
    if "youtube" in selected_sources:
        yt_items = fetch_youtube_search(keywords, limit=min(limit_per_src, 12)) or []
        for it in yt_items:
            tx = get_youtube_transcript(it.get("video_id")) if it.get("video_id") else None
            if tx:
                it["transcript_excerpt"] = tx[:600]
            posts.append(it)
        if yt_items:
            sources_used.append("YouTube")
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

# Profile
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
        per_topic=[dict(r) for r in per_topic],
    )

# Legacy Campaign helpers/routes (kept for compatibility)
SLUG_ALPHABET = "abcdefghjkmnpqrstuvwxyz23456789"
def _legacy_slug(n=8):
    return "".join(random.choice(SLUG_ALPHABET) for _ in range(n))

def _legacy_unique_slug():
    db = get_db()
    for _ in range(8):
        s = _legacy_slug()
        row = db.execute("SELECT 1 FROM campaigns WHERE slug = ?", (s,)).fetchone()
        if not row:
            return s
    return _legacy_slug() + str(int(time.time()))

def _iso_date_utc(d: datetime) -> str:
    return d.astimezone(timezone.utc).date().isoformat()

def _safe_sources_from_monitor(topic: str, max_urls=4):
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
        urls = [
            f"https://medlineplus.gov/search/?query={requests.utils.quote(topic)}",
            "https://www.cdc.gov/healthyliving/index.htm",
            "https://www.nih.gov/health-information",
        ]
    return list(dict.fromkeys(urls))[:max_urls]

def generate_weekly_plan(topic: str, audience: str, weeks: int = 4) -> list[dict]:
    subs = [
        "common myths", "warning signs", "benefits vs. risks", "reliability of sources",
        "interactions/contraindications", "age-specific considerations", "dosage and limits",
        "online misinformation tactics", "overhyped benefits", "peer pressure and trends"
    ]
    sources = _safe_sources_from_monitor(topic)
    def poster_body_for_week(week_no: int, subtheme: str) -> str:
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

def persist_campaign(user_id: int, title: str, topic: str, audience: str, visibility: str, starts_on: str, weeks: int, plan: list[dict]) -> int:
    db = get_db()
    slug = _legacy_unique_slug()
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


# ========= Quiz API =========
@app.post("/api/quiz/generate")
def api_quiz_generate():
    data = request.get_json(force=True, silent=True) or {}
    topic = (data.get("topic") or "").strip()
    if not topic:
        display_topic, mix_topics = composite_topic_for_today(
            g.user["id"] if g.user else None, max_terms=3
        )
        topic = display_topic
    else:
        mix_topics = [t.strip() for t in topic.split(",") if t.strip()]
    items = gpt_generate_mcqs(topic, n_questions=10)
    if len(items) < 10 and mix_topics:
        broader_topic = ", ".join(mix_topics) or topic
        more = gpt_generate_mcqs(broader_topic, n_questions=10)
        items = ensure_unique_items(items + more, topic="__mixed__")
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


# ========= Main =========
if __name__ == "__main__":
    # Make sure you have:
    # - OPENAI_API_KEY (and optionally OPENAI_IMAGE_MODEL, OPENAI_MODEL)
    # - YT_API_KEY (optional for YouTube API; RSS fallback is used otherwise)
    # - templates/* (including studio/ and campaigns/ views)
    # - static/posters/ directory (auto-created)
    app.run(debug=True)
