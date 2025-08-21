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

# =========================
# App & Config
# =========================
load_dotenv()
app = Flask(__name__)
app.secret_key = os.getenv("SECRET_KEY", "dev-secret-key-change-me")
COMMON_HEADERS = {"User-Agent": "EPICHECK/1.0 (+https://example.edu)"}

# SQLite file path (local)
DB_PATH = os.getenv("EPICHECK_DB", os.path.join(os.path.dirname(__file__), "epicheck.db"))

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

        CREATE INDEX IF NOT EXISTS idx_users_email ON users(email);
        CREATE INDEX IF NOT EXISTS idx_posts_search_id ON posts(search_id);
        CREATE INDEX IF NOT EXISTS idx_searches_created_at ON searches(created_at);

        -- ===== Quiz persistence (new) =====
        CREATE TABLE IF NOT EXISTS quizzes (
            id         INTEGER PRIMARY KEY AUTOINCREMENT,
            topic      TEXT NOT NULL,
            is_daily   INTEGER NOT NULL DEFAULT 0,  -- 1 for daily quiz
            created_at TEXT NOT NULL
        );

        CREATE TABLE IF NOT EXISTS quiz_items (
            id         INTEGER PRIMARY KEY AUTOINCREMENT,
            quiz_id    INTEGER NOT NULL,
            idx        INTEGER NOT NULL,            -- 0-based order
            q          TEXT NOT NULL,
            choices    TEXT NOT NULL,               -- JSON array of 4 strings
            answer_idx INTEGER NOT NULL,
            explain    TEXT,
            source     TEXT,
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
        -- One attempt per user OR per anon session for a given quiz
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
        """
    )
    # Lightweight migration in case "user_id" was missing on existing DB
    if not _col_exists(db, "searches", "user_id"):
        db.execute("ALTER TABLE searches ADD COLUMN user_id INTEGER")
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

def safe_get(url, headers=None, timeout=12, params=None):
    try:
        r = requests.get(url, headers=headers or COMMON_HEADERS, params=params, timeout=timeout)
        r.raise_for_status()
        return r
    except Exception:
        return None


# =========================
# Quiz generation (GPT)
# =========================
def gpt_generate_mcqs(topic: str, n_questions: int = 10):
    if not (_OPENAI_AVAILABLE and os.getenv("OPENAI_API_KEY")):
        return []

    schema_hint = textwrap.dedent(f"""
    Return STRICT JSON only. You may use either format:
    1) Top-level array of {n_questions} items:
       [
         {{"q":"...", "choices":["A","B","C","D"], "answer_idx":0,
           "explain":"...", "source":"https://(who.int|cdc.gov|nih.gov|ncbi.nlm.nih.gov|medlineplus.gov)/..."}},
         ...
       ]
    2) Or {{"items":[ ...same objects..., ({n_questions} total) ]}}

    Rules:
    - Exactly 4 options; one correct (answer_idx ∈ {{0,1,2,3}}).
    - Evidence-based; avoid absolute/unsafe claims.
    - Each item cites a canonical URL from WHO/CDC/NIH/NCBI/MedlinePlus.
    - If unsure: return {{"items": []}} or [].
    """)

    try:
        client = OpenAI(api_key=os.getenv("OPENAI_API_KEY"))
        resp = client.chat.completions.create(
            model=os.getenv("OPENAI_MODEL", "gpt-4o-mini"),
            temperature=0.3,
            messages=[
                {"role": "system",
                 "content": "You create safe, accurate health MCQs for teens. Output STRICT JSON only."},
                {"role": "user",
                 "content": f"Topic: {topic}\nCreate exactly {n_questions} items.\n\n{schema_hint}"}
            ]
        )
        raw = resp.choices[0].message.content
        data = json.loads(raw)
        items = data if isinstance(data, list) else data.get("items", [])
        valid = []
        for it in (items or []):
            if not isinstance(it, dict):
                continue
            choices = it.get("choices", [])
            src = (it.get("source") or "").strip()
            if (
                it.get("q")
                and isinstance(choices, list) and len(choices) == 4
                and isinstance(it.get("answer_idx"), int) and 0 <= it["answer_idx"] < 4
                and any(
                    src.startswith(f"https://{d}") or src.startswith(f"http://{d}")
                    for d in ["who.int", "cdc.gov", "nih.gov", "ncbi.nlm.nih.gov", "medlineplus.gov"]
                )
            ):
                valid.append({
                    "q": it["q"],
                    "choices": choices,
                    "answer_idx": it["answer_idx"],
                    "explain": it.get("explain", ""),
                    "source": src
                })
        return valid[:n_questions]
    except Exception:
        return []


# =========================
# Quiz generation (OSS fallback)
# =========================
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
                    "source": (contexts[0]["url"] if contexts else "")
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
    r = safe_get(url, params=params)
    if not r:
        return []
    try:
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
            dt = datetime.fromisoformat(published_at.replace("Z", "+00:00"))
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
        ))
    db.executemany(
        "INSERT INTO quiz_items (quiz_id, idx, q, choices, answer_idx, explain, source) VALUES (?, ?, ?, ?, ?, ?, ?)",
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
        "SELECT id, idx, q, choices, answer_idx, explain, source FROM quiz_items WHERE quiz_id = ? ORDER BY idx ASC",
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
            "source": r["source"] or ""
        })
    return items

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

# ---------- Profile / Dashboard ----------
def _rows_to_dicts(rows):
    return [dict(r) for r in rows] if rows else []

@app.template_filter("dt")
def _fmt_dt(val):
    if not val:
        return ""
    try:
        return datetime.fromisoformat(str(val).replace("Z", "+00:00")).strftime("%Y-%m-%d %H:%M")
    except Exception:
        return str(val)

# ---------- Profile / Dashboard ----------
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

    return render_template(
        "profile.html",
        is_guest=False,
        user=g.user,
        stats=dict(stats),
        attempts=[dict(r) for r in attempts],
        searches=[dict(r) for r in searches],
    )

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
    keywords = request.values.get("keywords", "").strip()
    selected_sources = request.values.getlist("sources") or ["youtube", "reddit"]
    selected_sources = [s for s in selected_sources if s in ("youtube", "reddit")]
    results = {"valid": [], "invalid": [], "uncertain": []}
    sources_used = []

    if request.method == "POST" and keywords:
        posts = []
        # ... (unchanged fetch + validate code) ...

        # Persist (attach user_id – guaranteed present due to @login_required)
        user_id = g.user["id"]
        search_id = save_monitor_search(keywords, sources_used or selected_sources, user_id)
        save_monitor_posts(search_id, results)

        session["last_results"] = results
        session["last_keywords"] = keywords
        session["last_search_id"] = search_id

    return render_template(
        "monitor.html",
        keywords=keywords,
        results=results,
        sources_used=sources_used,
        now=iso_now(),
        selected_sources=selected_sources
    )
@app.route("/quiz", methods=["GET", "POST"])
@login_required
def quiz():
    items = []
    points = 0
    topic = (request.values.get("topic") or "").strip() or (request.values.get("keywords") or "").strip()

    if request.method == "POST" and topic:
        # 1) Generate items (GPT -> OSS -> fallback)
        items_gen = gpt_generate_mcqs(topic, n_questions=10)
        if not items_gen:
            contexts = fetch_trusted_pages(get_trusted_sources_from_session_fallback(topic))
            items_gen = oss_generate_mcqs(topic, contexts) or []
        if not items_gen:
            items_gen = fallback_quiz(topic)

        # 2) Persist the quiz + items
        quiz_id = create_quiz(topic, is_daily=False, items=items_gen)
        session["active_quiz_id"] = quiz_id

        # 3) Create or reuse an attempt
        attempt = get_or_create_attempt(quiz_id)
        points = int(attempt["score"] or 0)

        # 4) Load items for template from DB
        items = get_quiz_items_for_template(quiz_id)

        return render_template("quiz.html", topic=topic, items=items, points=points)

    # GET: show current active quiz if any
    quiz_id = session.get("active_quiz_id")
    if quiz_id:
        items = get_quiz_items_for_template(quiz_id)
        attempt = get_or_create_attempt(quiz_id)
        points = int(attempt["score"] or 0)

    return render_template("quiz.html", topic=topic or "", items=items, points=points)


@app.route("/quiz/daily", methods=["GET"])
def quiz_daily():
    # Re-use today's daily quiz if already created; otherwise create and persist it.
    quiz_id = get_daily_quiz_today_id()
    if not quiz_id:
        topic = pick_daily_topic()
        items_gen = gpt_generate_mcqs(topic, n_questions=10)
        if not items_gen:
            contexts = fetch_trusted_pages(get_trusted_sources_from_session_fallback(topic))
            items_gen = oss_generate_mcqs(topic, contexts) or []
        if not items_gen:
            items_gen = fallback_quiz(topic)
        quiz_id = create_quiz(topic, is_daily=True, items=items_gen)

    session["active_quiz_id"] = quiz_id
    # Create or reuse attempt (per user/anon for this quiz)
    attempt = get_or_create_attempt(quiz_id)
    points = int(attempt["score"] or 0)
    # Load items for template
    items = get_quiz_items_for_template(quiz_id)

    # Determine topic for header
    db = get_db()
    topic_row = db.execute("SELECT topic FROM quizzes WHERE id = ?", (quiz_id,)).fetchone()
    topic = topic_row["topic"] if topic_row else ""

    return render_template("quiz.html", topic=topic, items=items, points=points)

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
# Fallback quiz generator
# =========================
def fallback_quiz(topic):
    items = []
    for i in range(10):
        items.append({
            "q": f"[Q {i+1}] Which statement about '{topic}' is most accurate?",
            "choices": [
                f"'{topic}' is always safe for everyone.",
                f"'{topic}' may carry risks and should not be considered a cure-all.",
                f"'{topic}' instantly cures most diseases.",
                "There is no need to consult credible sources about it."
            ],
            "answer_idx": 1,
            "explain": f"Authoritative sources (e.g., WHO/CDC) note that '{topic}' is not a miracle cure and can involve risks; evidence varies by context.",
            "source": "https://www.cdc.gov"
        })
    return items


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


# =========================
# Main
# =========================
if __name__ == "__main__":
    # Never hardcode API keys; set OPENAI_API_KEY and YT_API_KEY in your environment
    app.run(debug=True)
