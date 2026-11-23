"""Agent Office: a local dashboard that shows Orca agent sessions as staff in an office floor plan.

Each task (one instruction you sent) is filed into a department by the project folder it worked in,
so one session can show up in several departments. Only sessions open in Orca are shown.
Reads Orca's session journal (and OpenCode's DB for token/cost) in read-only mode.
Rename departments in departments.json.
Run: py -3.12 server.py [port] [--no-browser]
"""

import bisect
import collections
import ctypes
import gzip
import hashlib
import threading
import urllib.parse
import urllib.request
import json
import os
import re
import sqlite3
import sys
import time
import webbrowser
from datetime import datetime
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path

HERE = Path(__file__).resolve().parent
HOME = Path.home()
ORCA_DIR = Path(os.environ.get("APPDATA", "")) / "orca" if os.name == "nt" else HOME / ".orca"
# Orca moved its journal to agent-session-journal.db; the old domain file is the fallback.
ORCA_DB = ORCA_DIR / "agent-session-journal.db"
if not ORCA_DB.exists():
    ORCA_DB = ORCA_DIR / "agent-session-domain.db"
OPENCODE_DB = HOME / ".local" / "share" / "opencode" / "opencode.db"
DEPARTMENTS_FILE = HERE / "departments.json"
PRICING_FILE = HERE / "pricing.json"
PRICING_URL = "https://raw.githubusercontent.com/BerriAI/litellm/main/model_prices_and_context_window.json"
CLAUDE_PROJECTS = HOME / ".claude" / "projects"

TASK_WINDOW_MS = 24 * 60 * 60 * 1000
FEED_LIMIT = 40

# Built-in departments for work that isn't tied to a project folder.
# Project folders get their own department; name them in departments.json.
DEFAULT_DEPARTMENTS = {
    "_ops": {"name": "IT 인프라팀", "mission": "프로그램 설치, 환경 설정, 정리", "icon": "wrench", "color": "#94A3B8"},
    "_research": {"name": "리서치센터", "mission": "웹 검색과 자료 조사", "icon": "book", "color": "#A3E635"},
    "_desk": {"name": "질의응답 데스크", "mission": "도구 없이 바로 답한 질문", "icon": "help", "color": "#F472B6"},
    "_new": {"name": "입사 대기실", "mission": "아직 첫 지시를 받지 않은 세션", "icon": "users", "color": "#64748B"},
}
FALLBACK_COLORS = ["#FB923C", "#38BDF8", "#E879F9", "#4ADE80", "#F87171", "#818CF8"]

AVATAR_DIR = HERE / "avatars"
AVATAR_POSES = {"plain": "", "wave": "waveLongArm", "phone": "handPhone"}
AVATAR_URL = "https://api.dicebear.com/9.x/notionists/svg?seed={seed}&backgroundColor=transparent"


def avatar_svg(seed: str, pose: str):
    """Illustrated office worker (DiceBear Notionists), cached on disk so it works offline later."""
    seed = re.sub(r"[^A-Za-z0-9-]", "", seed)[:40]
    if not seed or pose not in AVATAR_POSES:
        return None
    path = AVATAR_DIR / f"{seed}-{pose}.svg"
    if path.exists():
        return path.read_bytes()
    url = AVATAR_URL.format(seed=urllib.parse.quote(seed))
    if AVATAR_POSES[pose]:
        url += f"&gesture={AVATAR_POSES[pose]}&gestureProbability=100"
    else:
        url += "&gestureProbability=0"
    try:
        with urllib.request.urlopen(url, timeout=6) as res:
            body = res.read()
    except OSError:
        return None
    AVATAR_DIR.mkdir(exist_ok=True)
    path.write_bytes(body)
    return body

WINDOWS_DIRS = {
    "appdata", "contacts", "desktop", "documents", "downloads", "favorites", "links", "music",
    "onedrive", "pictures", "saved games", "searches", "videos", "intel", "3d objects",
}
SYSTEM_RX = re.compile(r"appdata|program files|\\windows\\|downloads|winget|choco|pip install|npm i(nstall)? -g", re.I)
PROJECT_MARKERS = (
    ".git", "pyproject.toml", "package.json", "requirements.txt", "setup.py",
    "Cargo.toml", "go.mod", "pom.xml", "build.gradle",
)
CODE_EXTS = {".py", ".js", ".ts", ".tsx", ".jsx", ".html", ".go", ".rs", ".java", ".cs", ".cpp", ".c"}

_SEP = r"[\\/]+"
HOME_RX = re.compile(
    _SEP.join(re.escape(p.strip("\\/")) for p in HOME.parts if p.strip("\\/"))
    + _SEP
    + r"([^\\/\s'\";|,<>*?)]+)",
    re.I,
)

TOOL_CATEGORY = {
    "shell": "run", "bash": "run", "execute": "run",
    "read": "read", "glob": "read", "grep": "read", "list": "read",
    "edit": "edit", "write": "edit", "apply_patch": "edit", "multiedit": "edit",
    "webfetch": "web", "websearch": "web",
    "question": "ask",
    "subagent": "agent", "task": "agent", "skill": "agent",
}

# "pw: x", "token=x", "비밀번호는 x", "password is x": hide the value after the keyword.
SECRET_KEY_RX = re.compile(
    r"((?<![A-Za-z])(?:pwd|pw|password|pass|비밀번호|비번|암호|token|api[_ -]?key|secret)"
    r"(?:\s*[:=]\s*|(?:은|는|이|가)\s+|\s+is\s+))(\S+)",
    re.I,
)
# Password-looking words: letters/digits mixed with @ or ! (e.g. "abc123@@"). Shell syntax such as
# "$i", "2>&1" or "#22C55E" is left alone so commands stay readable.
SECRET_TOKEN_RX = re.compile(r"(?<![\w/\\@.])(?=[^\s/\\]*\d)(?=[^\s/\\]*[@!])[\w@!#.+-]{6,}(?![\w/\\])")


def mask(text):
    """Hide things that look like passwords or keys before they reach the screen."""
    if not text:
        return text
    text = SECRET_KEY_RX.sub(lambda m: m.group(1) + "••••", text)
    return SECRET_TOKEN_RX.sub("••••", text)


_project_cache = {}
_task_cache = {}


def is_project(folder: str) -> bool:
    key = folder.lower()
    if key in _project_cache:
        return _project_cache[key]
    path = HOME / folder
    ok = False
    if not folder.startswith(".") and key not in WINDOWS_DIRS and path.is_dir():
        if any((path / m).exists() for m in PROJECT_MARKERS):
            ok = True
        else:
            try:
                ok = any(p.suffix.lower() in CODE_EXTS for p in path.iterdir() if p.is_file())
            except OSError:
                ok = False
    _project_cache[key] = ok
    return ok


def canonical_folder(folder: str) -> str:
    try:
        for p in HOME.iterdir():
            if p.name.lower() == folder.lower():
                return p.name
    except OSError:
        pass
    return folder


_readme_cache = {}


def readme_title(folder: str) -> str:
    """First '# heading' of a project's README, used as the default department description."""
    if folder in _readme_cache:
        return _readme_cache[folder]
    title = ""
    for name in ("README.md", "readme.md", "README.MD", "Readme.md"):
        path = HOME / folder / name
        try:
            with open(path, encoding="utf-8", errors="replace") as fh:
                head = fh.read(4096)
        except OSError:
            continue
        for line in head.splitlines():
            if line.startswith("# "):
                title = line[2:].strip()
                break
        break
    _readme_cache[folder] = title
    return title


def read_departments_file() -> dict:
    try:
        data = json.loads(DEPARTMENTS_FILE.read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return {}
    return data if isinstance(data, dict) else {}


def write_departments_file(data: dict):
    tmp = DEPARTMENTS_FILE.with_name(DEPARTMENTS_FILE.name + ".tmp")
    tmp.write_text(json.dumps(data, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    os.replace(tmp, DEPARTMENTS_FILE)


def load_departments():
    if not DEPARTMENTS_FILE.exists():
        write_departments_file(DEFAULT_DEPARTMENTS)
    merged = {k.lower(): dict(v) for k, v in DEFAULT_DEPARTMENTS.items()}
    for k, v in read_departments_file().items():
        if isinstance(v, dict):
            merged[k.lower()] = {**merged.get(k.lower(), {}), **v}
    return merged


# ---------------------------------------------------------------- layout edits from the page

CEO_KEY = "_ceo"
KEY_RX = re.compile(r"^[\w.\- ]{1,100}$")
_conf_lock = threading.Lock()


def clean_text(value, limit):
    text = re.sub(r"[\x00-\x1f\x7f]", " ", str(value or "")).strip()
    return text[:limit]


def apply_layout_action(body) -> str:
    """Rename, reorder, hide or delete (merge) departments in departments.json. Returns an error or ''."""
    if not isinstance(body, dict):
        return "잘못된 요청입니다."
    action = body.get("action")

    def valid(key):
        return isinstance(key, str) and KEY_RX.match(key) is not None

    with _conf_lock:
        data = read_departments_file()

        def entry(key):
            key = key.lower()
            for k in data:
                if k.lower() == key and isinstance(data[k], dict):
                    return data[k]
            name = key if key.startswith("_") else canonical_folder(key)
            data[name] = {}
            return data[name]

        key = body.get("key")
        if action == "update":
            if not valid(key) or key == CEO_KEY:
                return "바꿀 부서를 찾지 못했습니다."
            e = entry(key)
            for field, limit in (("name", 40), ("mission", 80)):
                value = clean_text(body.get(field), limit)
                if value:
                    e[field] = value
                else:
                    e.pop(field, None)  # empty means "back to the default"
        elif action == "order":
            keys = body.get("keys")
            if not isinstance(keys, list) or len(keys) > 200 or not all(valid(k) for k in keys):
                return "배치 순서가 올바르지 않습니다."
            for i, k in enumerate(keys):
                entry(k)["order"] = i
        elif action == "resetOrder":
            for v in data.values():
                if isinstance(v, dict):
                    v.pop("order", None)
        elif action == "hide":
            if not valid(key) or key == CEO_KEY:
                return "숨길 부서를 찾지 못했습니다."
            if body.get("hidden"):
                entry(key)["hidden"] = True
            else:
                entry(key).pop("hidden", None)
        elif action == "delete":
            target = body.get("mergeInto")
            if not valid(key) or key == CEO_KEY or not valid(target) or target.lower() == key.lower():
                return "업무를 옮길 부서를 골라 주세요."
            e = entry(key)
            e["mergeInto"] = target.lower()
            e.pop("hidden", None)
        elif action == "restore":
            if not valid(key):
                return "되살릴 부서를 찾지 못했습니다."
            entry(key).pop("mergeInto", None)
        else:
            return "알 수 없는 요청입니다."

        # Entries left with nothing in them (and not a built-in) are noise in the file.
        for k in [k for k, v in data.items() if v == {} and k not in DEFAULT_DEPARTMENTS]:
            del data[k]
        write_departments_file(data)
    _state_cache["at"] = 0.0  # show the change on the next poll
    return ""


def resolve_department(key: str, conf: dict) -> str:
    """Follow 'deleted, tasks moved to X' links to the department that now owns the work."""
    seen = set()
    while key not in seen:
        seen.add(key)
        target = (conf.get(key) or {}).get("mergeInto")
        if not target:
            return key
        key = target.lower()
    return "_ops"


def department_name(key: str, conf: dict) -> str:
    c = conf.get(key) or {}
    if c.get("name"):
        return c["name"]
    return f"{canonical_folder(key)} 개발팀" if not key.startswith("_") else key


def connect(path: Path) -> sqlite3.Connection:
    conn = sqlite3.connect(f"file:{path}?mode=ro", uri=True, timeout=3)
    conn.row_factory = sqlite3.Row
    return conn


# ---------------------------------------------------------------- Orca 1.4.25x+ session store
# Newer Orca hosts (including remote daemons) keep the journal as revisioned outcomes
# (journal_outcomes: generation + entry_key + value_json) instead of journal_items rows.
# Rebuild the journal_items / journal_chat_state shape the rest of this file reads, and keep
# it up to date incrementally so a poll never re-parses the whole journal.

_v5 = {"view": None, "mark": {}, "generation": {}}


def has_table(conn: sqlite3.Connection, name: str) -> bool:
    return conn.execute(
        "select 1 from sqlite_master where type = 'table' and name = ?", (name,)
    ).fetchone() is not None


def row_count(conn: sqlite3.Connection, name: str) -> int:
    try:
        return conn.execute(f'select count(*) from "{name}"').fetchone()[0]
    except sqlite3.Error:
        return 0


def is_v5_store(conn: sqlite3.Connection) -> bool:
    return (
        has_table(conn, "journal_outcomes")
        and has_table(conn, "journal_outcome_generations")
        and not row_count(conn, "journal_items")
    )


def v5_item(session_id: str, entry_key: str, raw: str):
    try:
        item = json.loads(raw)
    except ValueError:
        return None
    body = item.get("body") or {}
    scope = item.get("turnScope") or {}
    seq = item.get("sequence") or 0
    return (
        session_id,
        entry_key,
        item.get("itemId") or "",
        scope.get("turnItemId"),
        body.get("kind") or "",
        body.get("role"),
        body.get("state"),
        0,
        seq,
        seq,
        item.get("observedAt") or 0,
        raw,
    )


def v5_build(conn: sqlite3.Connection) -> sqlite3.Connection:
    # The server answers on worker threads; collect_state() serializes access with _state_lock.
    view = sqlite3.connect(":memory:", check_same_thread=False)
    view.row_factory = sqlite3.Row
    view.execute(
        "create table journal_items (session_id text, entry_key text, item_id text,"
        " turn_item_id text, kind text, message_role text, lifecycle_state text, hidden integer,"
        " sequence integer, ordinal integer, observed_at integer, payload_json text)"
    )
    view.execute("create unique index journal_items_key on journal_items (session_id, entry_key)")
    view.execute("create table journal_chat_state (session_id text, last_activity_at integer, last_sequence integer)")
    view.execute("create table agent_session_tabs (tab_id text, session_id text, position integer)")
    view.execute("create table agent_session_records (session_id text, record_json text)")
    view.execute("create table office_aliases (alias text primary key, target text)")
    _v5["view"] = view
    _v5["mark"] = {}
    _v5["generation"] = {}
    v5_update(conn)
    return view


def v5_update(conn: sqlite3.Connection):
    """Apply only journal rows newer than the last poll."""
    view = _v5["view"]
    generations = {
        g: (sid, epoch)
        for g, sid, epoch in conn.execute(
            "select generation, session_id, epoch from journal_outcome_generations"
        )
    }
    for gen, (sid, _epoch) in generations.items():
        if _v5["generation"].get(sid) not in (None, gen):
            # The session moved to a fresh journal generation; its old items are gone.
            view.execute("delete from journal_items where session_id = ?", (sid,))
            _v5["mark"].pop(gen, None)
        _v5["generation"][sid] = gen
        top = conn.execute(
            "select max(seq) from journal_outcomes where generation = ?", (gen,)
        ).fetchone()[0] or 0
        since = _v5["mark"].get(gen, 0)
        if top <= since:
            continue
        for seq, key, raw, deleted in conn.execute(
            "select seq, entry_key, value_json, deleted from journal_outcomes"
            " where generation = ? and seq > ? and seq <= ? and field = 'items' order by seq",
            (gen, since, top),
        ):
            if deleted:
                view.execute("delete from journal_items where session_id = ? and entry_key = ?", (sid, key))
            else:
                item = v5_item(sid, key, raw)
                if item:
                    view.execute("insert or replace into journal_items values (?,?,?,?,?,?,?,?,?,?,?,?)", item)
        # A turn points at its prompt by an old provider id; the alias table links it to the item.
        for raw, deleted in conn.execute(
            "select value_json, deleted from journal_outcomes"
            " where generation = ? and seq > ? and seq <= ? and field = 'aliases' order by seq",
            (gen, since, top),
        ):
            try:
                pair = json.loads(raw)
            except ValueError:
                continue
            if not (isinstance(pair, list) and len(pair) == 2 and all(isinstance(x, str) for x in pair)):
                continue
            if deleted:
                view.execute("delete from office_aliases where alias = ?", (pair[0],))
            else:
                view.execute("insert or replace into office_aliases values (?, ?)", (pair[0], pair[1]))
        _v5["mark"][gen] = top
    view.execute("delete from journal_chat_state")
    view.execute(
        "insert into journal_chat_state"
        " select session_id, max(observed_at), max(sequence) from journal_items group by session_id"
    )
    for table in ("agent_session_tabs", "agent_session_records"):
        if not has_table(conn, table):
            continue
        view.execute(f'delete from "{table}"')
        cols = [r[1] for r in conn.execute(f'pragma table_info("{table}")')]
        placeholders = ", ".join("?" * len(cols))
        view.executemany(
            f'insert into "{table}" values ({placeholders})',
            [tuple(r) for r in conn.execute(f'select * from "{table}"')],
        )
    view.commit()


def open_store(path: Path) -> sqlite3.Connection:
    conn = connect(path)
    if not is_v5_store(conn):
        _v5["view"] = None
        return conn
    try:
        view = _v5["view"]
        if view is None:
            view = v5_build(conn)
        else:
            v5_update(conn)
    finally:
        conn.close()
    return view


def close_store(conn: sqlite3.Connection):
    """Keep the cached v5 view open across polls; close everything else."""
    if conn is not _v5["view"]:
        conn.close()


def pid_alive(pid) -> bool:
    if not pid:
        return False
    if os.name != "nt":
        try:
            os.kill(int(pid), 0)
            return True
        except OSError:
            return False
    kernel32 = ctypes.windll.kernel32
    handle = kernel32.OpenProcess(0x1000, False, int(pid))
    if not handle:
        return False
    try:
        code = ctypes.c_ulong()
        ok = kernel32.GetExitCodeProcess(handle, ctypes.byref(code))
        return bool(ok) and code.value == 259
    finally:
        kernel32.CloseHandle(handle)


# ---------------------------------------------------------------- recent activity / live status

FEED_SQL = """
select kind, message_role as role, lifecycle_state as state, sequence,
  json_extract(payload_json, '$.observedAt') as at,
  json_extract(payload_json, '$.body.name') as tool,
  json_extract(payload_json, '$.body.path') as path,
  json_extract(payload_json, '$.body.exitCode') as exit_code,
  substr(coalesce(
    json_extract(payload_json, '$.body.input.description'),
    json_extract(payload_json, '$.body.input.command'),
    json_extract(payload_json, '$.body.input.path'),
    json_extract(payload_json, '$.body.input.filePath'),
    json_extract(payload_json, '$.body.input.pattern'),
    json_extract(payload_json, '$.body.input.url'),
    json_extract(payload_json, '$.body.input.query'),
    json_extract(payload_json, '$.body.input.id'),
    json_extract(payload_json, '$.body.input.questions[0].header'),
    json_extract(payload_json, '$.body.input.prompt'),
    json_extract(payload_json, '$.body.questions[0].header'),
    json_extract(payload_json, '$.body.question'),
    ''), 1, 1000) as detail,
  substr(json_extract(payload_json, '$.body.blocks[0].text'), 1, 1500) as text,
  case
    when kind = 'question' then json_extract(payload_json, '$.body.questions')
    when kind = 'tool-call' and json_extract(payload_json, '$.body.name') = 'question'
      then json_extract(payload_json, '$.body.input.questions')
  end as questions
from journal_items
where rowid in (
  -- Pick the newest rows first so the JSON is only parsed for those, not the whole history.
  select rowid from journal_items
  where session_id = ? and hidden = 0 and kind in ('tool-call', 'diff', 'message', 'question', 'turn')
  order by sequence desc, ordinal desc
  limit ?
) and session_id = ?
order by sequence desc, ordinal desc
"""


def load_feed(conn, sid):
    feed = []
    for r in conn.execute(FEED_SQL, (sid, FEED_LIMIT, sid)):
        kind = r["kind"]
        e = {"at": r["at"], "kind": kind, "state": r["state"], "seq": r["sequence"]}
        if kind == "tool-call":
            e.update(tool=r["tool"], cat=TOOL_CATEGORY.get(r["tool"], "other"),
                     detail=mask((r["detail"] or "").strip()), exitCode=r["exit_code"])
        elif kind == "message":
            e.update(role=r["role"], text=mask((r["text"] or "").strip()))
        elif kind == "diff":
            e.update(cat="edit", path=r["path"])
        elif kind == "question":
            e.update(cat="ask", detail=mask((r["detail"] or "").replace("Questions\n\n", "").strip()))
        headers = question_headers(r["questions"])
        if headers:
            e.update(detail=mask(", ".join(headers)), count=len(headers))
        feed.append(e)
    return feed


def question_headers(raw):
    """Short titles of every question in one approval request."""
    try:
        items = json.loads(raw) if raw else None
    except ValueError:
        return []
    out = []
    for q in items if isinstance(items, list) else []:
        if not isinstance(q, dict):
            continue
        title = q.get("header")
        if not title:
            lines = [ln.strip() for ln in str(q.get("question") or "").splitlines() if ln.strip() and ln.strip() != "Questions"]
            title = lines[0] if lines else ""
        if title:
            out.append(title)
    return out


def latest_turn(conn, sid):
    row = conn.execute(
        "select lifecycle_state as state, sequence, json_extract(payload_json, '$.body.startedAt') as started_at,"
        " json_extract(payload_json, '$.observedAt') as at"
        " from journal_items where session_id = ? and kind = 'turn' order by sequence desc limit 1",
        (sid,),
    ).fetchone()
    return dict(row) if row else None


def derive_status(live, feed, last_turn, turn):
    started = None
    if turn:
        running = turn["state"] == "running"
        started = turn.get("started_at") or turn.get("at")
    else:
        running = bool(last_turn and last_turn.get("state") == "open")
    if not running and turn:
        # Work can continue after a turn closes (follow-ups scoped to the thread, not a prompt).
        after = [f for f in feed if f["seq"] > turn["sequence"] and f["kind"] != "turn"]
        if any(
            (f["kind"] == "tool-call" and f["state"] == "running")
            or (f["kind"] == "question" and f["state"] not in ("resolved", "cancelled"))
            for f in after
        ):
            running = True
            started = min(f["at"] for f in after if f["at"])
    if not feed and not last_turn:
        return ("idle" if live else "empty"), None, None
    if not live:
        return "offline", None, None
    if not running:
        return "idle", None, None

    started = started or (last_turn or {}).get("at")
    for f in feed:
        if f["kind"] == "turn":
            break
        if f["kind"] == "question" and f["state"] not in ("resolved", "cancelled"):
            return "waiting", f, started
        if f["kind"] == "tool-call" and f["state"] == "running":
            return ("waiting" if f.get("tool") == "question" else "working"), f, started
    latest = next((f for f in feed if f["kind"] != "turn"), None)
    if latest and latest["kind"] == "message" and latest.get("role") == "assistant":
        return "writing", latest, started
    if latest and latest["kind"] in ("tool-call", "diff"):
        return "working", latest, started
    return "thinking", latest, started


# ---------------------------------------------------------------- tasks (one per instruction)

TASK_SQL = """
select kind, message_role as role, lifecycle_state as state, ordinal, item_id, turn_item_id,
  json_extract(payload_json, '$.observedAt') as at,
  json_extract(payload_json, '$.body.name') as tool,
  case when kind = 'tool-call' then substr(json_extract(payload_json, '$.body.input'), 1, 3000) end as input,
  json_extract(payload_json, '$.body.path') as path,
  json_extract(payload_json, '$.body.userItemId') as user_item,
  json_extract(payload_json, '$.body.startedAt') as started_at,
  json_extract(payload_json, '$.body.completedAt') as completed_at,
  json_extract(payload_json, '$.body.outcome') as outcome,
  case when kind = 'message' and message_role in ('user', 'assistant')
    then substr(json_extract(payload_json, '$.body.blocks[0].text'), 1, 4000) end as text
from journal_items
where session_id = ? and hidden = 0 and kind in ('turn', 'tool-call', 'diff', 'message', 'question')
order by ordinal
"""


def build_tasks(conn, sid):
    tasks, by_item, prompts = [], {}, {}
    current = None
    last_prompt = ("", 0)
    try:
        aliases = dict(conn.execute("select alias, target from office_aliases"))
    except sqlite3.Error:
        aliases = {}
    for r in conn.execute(TASK_SQL, (sid,)):
        kind = r["kind"]
        if kind == "turn":
            started = r["started_at"] or r["at"]
            current = {
                "id": r["item_id"],
                "sid": sid,
                "userItem": r["user_item"],
                # Continuation turns have no new prompt; keep the one they follow.
                "_hint": last_prompt[0] if last_prompt[1] and last_prompt[1] <= (started or 0) else "",
                "startedAt": started,
                "endedAt": r["completed_at"],
                "lastAt": r["completed_at"] or r["started_at"] or r["at"],
                "state": r["state"] or "completed",
                "outcome": r["outcome"],
                "reply": None,
                "tools": collections.Counter(),
                "files": [],
                "_score": collections.Counter(),
                "_system": 0,
            }
            tasks.append(current)
            by_item[r["item_id"]] = current
            continue
        if kind == "message" and r["role"] == "user":
            prompts[r["item_id"]] = r["text"]
            last_prompt = (r["text"] or "", r["at"] or 0)
            continue
        owner = by_item.get(r["turn_item_id"]) if r["turn_item_id"] else None
        owner = owner or current
        if owner is None:
            continue
        if r["at"]:
            owner["lastAt"] = max(owner["lastAt"] or 0, r["at"])
        if kind == "message":
            if r["role"] == "assistant" and r["text"]:
                owner["reply"] = r["text"]
        elif kind == "tool-call":
            owner["tools"][TOOL_CATEGORY.get(r["tool"], "other")] += 1
            text = r["input"] or ""
            for folder in HOME_RX.findall(text):
                if is_project(folder):
                    owner["_score"][folder.lower()] += 1
            if SYSTEM_RX.search(text):
                owner["_system"] += 1
        elif kind == "diff" and r["path"]:
            path = r["path"].replace("\\\\", "\\")
            if path not in owner["files"]:
                owner["files"].append(path)
            for folder in HOME_RX.findall(path):
                if is_project(folder):
                    owner["_score"][folder.lower()] += 3
        elif kind == "question":
            owner["tools"]["ask"] += 1

    previous_project = None
    for t in tasks:
        user_item = t.pop("userItem")
        for _ in range(8):
            target = aliases.get(user_item)
            if not target or target == user_item:
                break
            user_item = target
        hint = t.pop("_hint", "")
        prompt = mask((prompts.get(user_item) or hint or "").strip())
        t["prompt"] = prompt
        t["reply"] = mask(t["reply"])
        first = next((line.strip() for line in prompt.splitlines() if line.strip()), "")
        # Continuation turns share their prompt with the task before them; say so.
        t["title"] = first + (" · 계속" if first and hint and not prompts.get(user_item) else "")
        tools = t["tools"]
        total = sum(tools.values())
        score, system = t.pop("_score"), t.pop("_system")
        if score:
            top, top_score = score.most_common(1)[0]
            prev_score = score.get(previous_project, 0) if previous_project else 0
            # Stay with the session's ongoing project unless the other folder clearly dominates:
            # a single passing mention (e.g. checking another app's process) is not a move.
            if previous_project and top != previous_project and (prev_score * 2 >= top_score or (prev_score == 0 and top_score < 3)):
                dept = previous_project
            else:
                dept = canonical_folder(top).lower()
            previous_project = dept
        elif total == 0:
            # A task cut off (or just started) before using tools stays with the work it continues.
            dept = "_desk" if t["state"] == "completed" or not previous_project else previous_project
        elif tools["web"] >= max(1, total / 2) and not tools["edit"]:
            dept = "_research"
        elif previous_project and not system:
            dept = previous_project
        else:
            dept = "_ops"
        t["dept"] = dept
        if tools["edit"] or t["files"]:
            t["kind"] = "edit"
        elif total == 0:
            t["kind"] = "answer"
        else:
            t["kind"] = max(("web", "run", "read", "ask", "agent"), key=lambda k: tools[k])
        t["tools"] = dict(tools)
        if not t["title"]:
            # Continuations have no new prompt; name them after what they touched.
            if t["files"]:
                name = t["files"][0].replace("\\", "/").rsplit("/", 1)[-1]
                extra = len(t["files"]) - 1
                t["title"] = f"{name} 수정" + (f" 외 {extra}개" if extra > 0 else "")
            elif t["reply"]:
                t["title"] = next((line.strip() for line in t["reply"].splitlines() if line.strip()), "")[:80]
            else:
                t["title"] = "이어서 진행한 업무"
        t["fileCount"] = len(t["files"])
        t["files"] = t["files"][:40]
    return tasks


_journal_cache = {}


def session_journal(conn, sid, version):
    """Recent activity and latest turn; only re-read when the session's journal changes."""
    cached = _journal_cache.get(sid)
    if cached and cached[0] == version:
        return cached[1]
    result = (load_feed(conn, sid), latest_turn(conn, sid))
    _journal_cache[sid] = (version, result)
    return result


def session_tasks(conn, sid, version):
    cached = _task_cache.get(sid)
    if cached and cached[0] == version:
        return cached[1]
    tasks = build_tasks(conn, sid)
    _task_cache[sid] = (version, tasks)
    return tasks


_oc_cache = [None, ({}, {})]


def file_stamp(*paths):
    out = []
    for p in paths:
        try:
            st = p.stat()
            out.append((st.st_mtime_ns, st.st_size))
        except OSError:
            out.append(None)
    return tuple(out)


def opencode_stats():
    """Same as load_opencode_stats, re-read only when OpenCode's database files change."""
    stamp = file_stamp(OPENCODE_DB, OPENCODE_DB.with_name(OPENCODE_DB.name + "-wal"))
    if _oc_cache[0] != stamp:
        _oc_cache[1] = load_opencode_stats()
        _oc_cache[0] = stamp
    return _oc_cache[1]


def load_opencode_stats():
    """Session totals plus each reply's cost, so cost can be split per task."""
    if not OPENCODE_DB.exists():
        return {}, {}
    try:
        conn = connect(OPENCODE_DB)
        rows = conn.execute(
            "select id, title, cost, tokens_input, tokens_output, tokens_reasoning, tokens_cache_read from session_v2"
        ).fetchall()
        msgs = conn.execute(
            "select session_id, time_created as at, json_extract(data, '$.cost') as cost,"
            " coalesce(json_extract(data, '$.tokens.input'), 0) + coalesce(json_extract(data, '$.tokens.output'), 0)"
            " + coalesce(json_extract(data, '$.tokens.reasoning'), 0) + coalesce(json_extract(data, '$.tokens.cache.read'), 0)"
            " + coalesce(json_extract(data, '$.tokens.cache.write'), 0) as tokens"
            " from session_message where type = 'assistant' and json_extract(data, '$.cost') is not null"
            " order by time_created"
        ).fetchall()
        conn.close()
    except sqlite3.Error:
        return {}, {}
    totals = {
        r["id"]: {
            "title": r["title"],
            "cost": r["cost"],
            "tokensIn": r["tokens_input"] + r["tokens_cache_read"],
            "tokensOut": r["tokens_output"] + r["tokens_reasoning"],
        }
        for r in rows
    }
    per_reply = collections.defaultdict(list)
    for m in msgs:
        per_reply[m["session_id"]].append((m["at"], m["cost"] or 0.0, m["tokens"] or 0))
    return totals, per_reply


def cumulative(replies, max_points=240):
    """Running total of cost over time, thinned out for charting."""
    points, total = [], 0.0
    for r in replies:
        total += r[1]
        points.append([r[0], round(total, 4)])
    if len(points) > max_points:
        step = len(points) / max_points
        points = [points[int(i * step)] for i in range(max_points)] + [points[-1]]
    return points


def attach_costs(tasks, replies):
    starts = [t["startedAt"] or 0 for t in tasks]
    for t in tasks:
        t["cost"], t["tokens"] = 0.0, 0
    if not tasks or not replies:
        for t in tasks:
            t["cost"] = None
        return
    for r in replies:
        at, cost, tok = r[0], r[1], r[2]
        i = max(0, bisect.bisect_right(starts, at) - 1)
        tasks[i]["cost"] += cost
        tasks[i]["tokens"] += tok


# ---------------------------------------------------------------- API prices and real token cost
# Orca's journal only keeps rough context sizes, so money comes from the provider's own usage
# records: Claude Code writes one JSONL per session under ~/.claude/projects with exact token
# counts. pricing.json holds USD per 1M tokens (input, output, cache write, cache read).

_pricing = {"models": {}, "at": 0.0}
_transcripts = {}
_transcript_lock = threading.Lock()


def read_pricing_file() -> dict:
    try:
        data = json.loads(PRICING_FILE.read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return {}
    models = data.get("models") or {}
    return {
        str(k).lower(): [float(x) for x in v[:4]]
        for k, v in models.items()
        if isinstance(v, list) and len(v) >= 2
    }


def refresh_pricing():
    """Pull today's API prices once in the background; pricing.json stays the offline fallback."""
    try:
        with urllib.request.urlopen(PRICING_URL, timeout=20) as res:
            data = json.load(res)
    except (OSError, ValueError):
        return
    models = {}
    for name, v in data.items():
        if "/" in name or not isinstance(v, dict):
            continue
        inp, out = v.get("input_cost_per_token"), v.get("output_cost_per_token")
        if inp is None or out is None:
            continue
        models[name.lower()] = [
            inp * 1e6,
            out * 1e6,
            (v.get("cache_creation_input_token_cost") or 0) * 1e6,
            (v.get("cache_read_input_token_cost") or 0) * 1e6,
        ]
    if models:
        with _transcript_lock:
            _pricing["models"] = models
            _pricing["at"] = time.time()


def price_for(model):
    """USD per 1M tokens for a model id, matching the longest known name first."""
    key = (model or "").strip().lower()
    if not key or key.startswith("<"):
        return None
    table = _pricing["models"]
    if key in table:
        return table[key]
    best = None
    for name, price in table.items():
        if key.startswith(name) and (best is None or len(name) > len(best[0])):
            best = (name, price)
    if best:
        return best[1]
    for family in ("opus", "sonnet", "haiku", "codex", "gpt-5", "gemini"):
        if family in key:
            for name, price in table.items():
                if name.startswith("claude-" + family) or name.startswith(family):
                    return price
    return None


def iso_ms(value):
    if not value:
        return 0
    try:
        return int(datetime.fromisoformat(str(value).replace("Z", "+00:00")).timestamp() * 1000)
    except ValueError:
        return 0


def transcript_paths(native_id):
    if not native_id or not CLAUDE_PROJECTS.is_dir():
        return []
    return sorted(str(p) for p in CLAUDE_PROJECTS.glob(f"*/{native_id}.jsonl"))


def scan_transcript(path, state):
    """Read only the bytes appended since the last poll and price each assistant reply."""
    try:
        st = os.stat(path)
    except OSError:
        return
    stamp = (st.st_mtime_ns, st.st_size)
    if state.get("stamp") == stamp:
        return
    try:
        with open(path, "rb") as fh:
            fh.seek(state.get("offset", 0))
            chunk = fh.read()
    except OSError:
        return
    state["offset"] = state.get("offset", 0) + len(chunk)
    state["stamp"] = stamp
    lines = (state.get("partial", "") + chunk.decode("utf-8", "replace")).split("\n")
    state["partial"] = lines.pop()  # a half-written last line waits for the next poll
    replies = state.setdefault("replies", [])
    for line in lines:
        if '"usage"' not in line:
            continue
        try:
            rec = json.loads(line)
        except ValueError:
            continue
        msg = rec.get("message") or {}
        usage = msg.get("usage") or {}
        price = price_for(msg.get("model"))
        if not usage or not price:
            continue
        cached = usage.get("cache_read_input_tokens") or 0
        tin = (usage.get("input_tokens") or 0) + (usage.get("cache_creation_input_tokens") or 0) + cached
        tout = usage.get("output_tokens") or 0
        cost = (
            (usage.get("input_tokens") or 0) * price[0]
            + tout * price[1]
            + (usage.get("cache_creation_input_tokens") or 0) * (price[2] or price[0])
            + cached * (price[3] if len(price) > 3 else price[0] / 10)
        ) / 1e6
        replies.append((iso_ms(rec.get("timestamp")), cost, tin + tout, tin, tout))


def claude_usage(native_id):
    """Per-reply cost and session totals from Claude Code's token records."""
    if not native_id:
        return None, None
    with _transcript_lock:
        entry = _transcripts.get(native_id)
        if entry is None:
            entry = _transcripts[native_id] = {"paths": transcript_paths(native_id), "files": {}}
        if not entry["paths"]:
            return None, None
        for path in entry["paths"]:
            scan_transcript(path, entry["files"].setdefault(path, {}))
        replies = sorted(
            (r for f in entry["files"].values() for r in f.get("replies", [])),
            key=lambda r: r[0],
        )
    if not replies:
        return None, None
    totals = {
        "cost": sum(r[1] for r in replies),
        "tokensIn": sum(r[3] for r in replies),
        "tokensOut": sum(r[4] for r in replies),
    }
    return replies, totals


_pricing["models"] = read_pricing_file()


def collect_state():
    now = int(time.time() * 1000)
    if not ORCA_DB.exists():
        return {"now": now, "error": f"Orca 기록 파일을 찾을 수 없습니다: {ORCA_DB}", "sessions": [], "tasks": [], "departments": []}

    dept_conf = load_departments()
    conn = open_store(ORCA_DB)
    try:
        tabs = {r["session_id"]: r["position"] for r in conn.execute("select session_id, position from agent_session_tabs")}
        chat = {
            r["session_id"]: (r["last_activity_at"], r["last_sequence"])
            for r in conn.execute("select session_id, last_activity_at, last_sequence from journal_chat_state")
        }
        records = {}
        for r in conn.execute("select session_id, record_json from agent_session_records"):
            if r["session_id"] in tabs:
                records[r["session_id"]] = json.loads(r["record_json"])
        oc, oc_replies = opencode_stats()

        sessions, all_tasks, cost_series = [], [], {}
        for sid, rec in records.items():
            last_turn = rec.get("lastTurn")
            activity, version = chat.get(sid, (0, 0))
            lease = rec.get("lease") or {}
            owner = lease.get("ownerProcess") or {}
            live = lease.get("claimStatus") == "live" and pid_alive(owner.get("pid"))

            feed, turn = session_journal(conn, sid, version)
            status, current, active_since = derive_status(live, feed, last_turn, turn)
            tasks = [dict(t) for t in session_tasks(conn, sid, version)]
            # A session works inside one worktree; that is a better department than whatever
            # folder a single tool call happened to mention.
            workspace = str((rec.get("location") or {}).get("workspaceId") or "")
            workspace = workspace.split("::")[-1].rstrip("/\\").replace("\\", "/")
            workspace = workspace.rsplit("/", 1)[-1]
            for t in tasks:
                t["dept"] = resolve_department(workspace or t["dept"], dept_conf)
            if tasks and status in ("working", "thinking", "writing", "waiting"):
                tasks[-1]["state"] = "running"
                tasks[-1]["endedAt"] = None
            for t in tasks:
                if t["state"] == "running" and status not in ("working", "thinking", "writing", "waiting"):
                    t["state"] = "interrupted" if status == "offline" else "completed"
                    t["endedAt"] = t["endedAt"] or t["lastAt"]

            chain = rec.get("providerHandleChain") or []
            handle = (chain[-1].get("handle") if chain else None) or {}
            native_id = handle.get("nativeId") or handle.get("sessionId")
            stats = oc.get(native_id) if native_id else None
            replies = oc_replies.get(native_id) if native_id else None
            if not replies:
                # Claude Code keeps the exact token counts Orca's journal lacks.
                replies, stats = claude_usage(native_id)
            attach_costs(tasks, replies)
            if replies:
                cost_series[sid] = cumulative(replies)
            name = rec.get("conversationName") or (stats or {}).get("title") or ""
            first_title = tasks[0]["title"] if tasks else ""
            # Orca shortens long names with an ellipsis; use the full first instruction instead.
            if not name or (name.rstrip().endswith(("…", "...")) and first_title):
                name = first_title or name
            name = mask(name)

            home = tasks[-1]["dept"] if tasks else resolve_department("_new", dept_conf)
            files = {f for t in tasks for f in t["files"]}
            sessions.append(
                {
                    "id": sid,
                    "name": name.strip(),
                    "provider": rec.get("provider"),
                    "model": (rec.get("options") or {}).get("model"),
                    "effort": (rec.get("options") or {}).get("effort"),
                    "tab": tabs[sid],
                    "createdAt": rec.get("createdAt"),
                    "lastActivity": activity or rec.get("updatedAt"),
                    "live": live,
                    "status": status,
                    "current": current,
                    "activeSince": active_since,
                    "home": home,
                    "currentTask": tasks[-1]["id"] if tasks else None,
                    "taskCount": len(tasks),
                    "fileCount": len(files),
                    "tools": dict(sum((collections.Counter(t["tools"]) for t in tasks), collections.Counter())),
                    "usage": stats and {k: stats[k] for k in ("cost", "tokensIn", "tokensOut")},
                    "feed": [f for f in feed if f["kind"] != "turn"][:14],
                }
            )
            for t in tasks:
                if t["state"] == "running" or now - (t["lastAt"] or 0) < TASK_WINDOW_MS:
                    all_tasks.append(t)
    finally:
        close_store(conn)

    for cache in (_task_cache, _journal_cache):
        for gone in set(cache) - set(records):
            cache.pop(gone, None)

    sessions.sort(key=lambda s: s["tab"])
    all_tasks.sort(key=lambda t: t["startedAt"] or 0)

    keys = list(dict.fromkeys([t["dept"] for t in all_tasks] + [s["home"] for s in sessions]))
    departments = []
    used_colors = set()
    for i, key in enumerate(keys):
        conf = dept_conf.get(key) or {}
        folder = None if key.startswith("_") else canonical_folder(key)
        color = conf.get("color")
        if not color:
            color = next((c for c in FALLBACK_COLORS if c not in used_colors), FALLBACK_COLORS[i % len(FALLBACK_COLORS)])
        used_colors.add(color)
        dtasks = [t for t in all_tasks if t["dept"] == key]
        departments.append(
            {
                "key": key,
                "name": conf.get("name") or f"{folder} 개발팀",
                "mission": conf.get("mission") or (readme_title(folder) if folder else ""),
                "icon": conf.get("icon") or "code",
                "color": color,
                "folder": str(HOME / folder) if folder else None,
                "support": key.startswith("_"),
                "taskCount": len(dtasks),
                "fileCount": len({f for t in dtasks for f in t["files"]}),
                "workMs": sum(((t["endedAt"] or now) - (t["startedAt"] or now)) for t in dtasks),
                "cost": sum(t["cost"] or 0 for t in dtasks),
                "staff": [s["id"] for s in sessions if s["home"] == key],
                "order": conf.get("order"),
                "hidden": bool(conf.get("hidden")),
                "custom": {k: conf[k] for k in ("name", "mission") if conf.get(k)},
            }
        )

    present = set(keys)
    layout = {
        "ceoOrder": (dept_conf.get(CEO_KEY) or {}).get("order"),
        # Hidden departments with no work right now still need a "show again" button.
        "hiddenIdle": [
            {"key": k, "name": department_name(k, dept_conf)}
            for k, v in dept_conf.items()
            if v.get("hidden") and not v.get("mergeInto") and k not in present and k != CEO_KEY
        ],
        "removed": [
            {"key": k, "name": department_name(k, dept_conf), "mergeInto": v["mergeInto"],
             "targetName": department_name(resolve_department(v["mergeInto"], dept_conf), dept_conf)}
            for k, v in dept_conf.items()
            if v.get("mergeInto")
        ],
        "targets": [{"key": d["key"], "name": d["name"]} for d in departments]
        + [
            {"key": k, "name": department_name(k, dept_conf)}
            for k in ("_ops", "_research", "_desk")
            if k not in present and not (dept_conf.get(k) or {}).get("mergeInto")
        ],
    }
    return {"sessions": sessions, "tasks": all_tasks, "departments": departments, "costSeries": cost_series,
            "layout": layout}


STATE_TTL = 1.0
_state_lock = threading.Lock()
_state_cache = {"at": 0.0, "body": b"", "gzip": b"", "etag": ""}


def state_payload():
    """Serialized state shared by every open tab for up to a second, with its gzip copy and ETag."""
    with _state_lock:
        if time.time() - _state_cache["at"] >= STATE_TTL:
            try:
                data = collect_state()
            except Exception as exc:  # Orca may be mid-write; the page keeps its last good state
                data = {"error": f"상태를 읽지 못했습니다: {exc}", "sessions": None}
            body = json.dumps(data, ensure_ascii=False).encode("utf-8")
            _state_cache.update(
                at=time.time(),
                body=body,
                gzip=gzip.compress(body, compresslevel=5),
                etag='"' + hashlib.sha1(body).hexdigest()[:20] + '"',
            )
        return dict(_state_cache)


VENDOR_DIR = HERE / "vendor"
VENDOR = {
    "echarts.min.js": "https://cdn.jsdelivr.net/npm/echarts@5.5.1/dist/echarts.min.js",
}


def vendor_file(name: str):
    """Third-party script, downloaded once and then served locally so charts also work offline."""
    url = VENDOR.get(name)
    if not url:
        return None
    path = VENDOR_DIR / name
    if path.exists():
        return path.read_bytes()
    try:
        with urllib.request.urlopen(url, timeout=15) as res:
            body = res.read()
    except OSError:
        return None
    VENDOR_DIR.mkdir(exist_ok=True)
    path.write_bytes(body)
    return body


ALLOWED_HOSTS = {"127.0.0.1", "localhost", "[::1]"}


class Handler(BaseHTTPRequestHandler):
    def log_message(self, *args):
        pass

    def send(self, code, body: bytes, ctype: str, cache: str = "no-store", headers=None):
        try:
            self.send_response(code)
            self.send_header("Content-Type", ctype)
            self.send_header("Cache-Control", cache)
            for k, v in (headers or {}).items():
                self.send_header(k, v)
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            if self.command != "HEAD":
                self.wfile.write(body)
        except (BrokenPipeError, ConnectionResetError, ConnectionAbortedError):
            pass  # the browser closed the tab mid-response

    def host_allowed(self) -> bool:
        # Refuse requests addressed to other host names (DNS rebinding from a web page).
        host = (self.headers.get("Host") or "").strip().lower()
        if host.startswith("["):
            name = host.split("]")[0] + "]"
        else:
            name = host.split(":")[0]
        return name in ALLOWED_HOSTS

    def do_HEAD(self):
        self.do_GET()

    def do_POST(self):
        # Changes only come from our own page: a custom header can't be sent cross-site without a
        # CORS preflight (which this server never approves), and the Origin must be this server.
        origin = self.headers.get("Origin")
        origin_ok = origin is None or re.match(r"^http://(127\.0\.0\.1|localhost|\[::1\]):\d+$", origin)
        if not self.host_allowed() or self.headers.get("X-Agent-Office") != "1" or not origin_ok:
            self.send(403, b"forbidden", "text/plain")
            return
        if self.path.split("?", 1)[0] != "/api/departments":
            self.send(404, b"not found", "text/plain")
            return
        try:
            length = int(self.headers.get("Content-Length") or 0)
        except ValueError:
            length = -1
        if length < 0 or length > 20000:
            self.send(413, b"too large", "text/plain")
            return
        try:
            body = json.loads(self.rfile.read(length) or b"{}")
        except ValueError:
            body = None
        error = apply_layout_action(body)
        out = json.dumps({"ok": not error, "error": error}, ensure_ascii=False).encode("utf-8")
        self.send(400 if error else 200, out, "application/json; charset=utf-8")

    def do_GET(self):
        if not self.host_allowed():
            self.send(403, b"forbidden", "text/plain")
            return
        path = self.path.split("?", 1)[0]
        if path == "/api/ping":
            self.send(200, b'{"app": "agent-office"}', "application/json")
        elif path == "/api/state":
            state = state_payload()
            if self.headers.get("If-None-Match") == state["etag"]:
                self.send(304, b"", "application/json", headers={"ETag": state["etag"]})
                return
            headers = {"ETag": state["etag"], "Vary": "Accept-Encoding"}
            body = state["body"]
            if "gzip" in (self.headers.get("Accept-Encoding") or ""):
                body = state["gzip"]
                headers["Content-Encoding"] = "gzip"
            self.send(200, body, "application/json; charset=utf-8", "no-cache", headers)
        elif path.startswith("/avatar/"):
            parts = path.split("/")
            body = avatar_svg(parts[2], parts[3].removesuffix(".svg")) if len(parts) == 4 else None
            if body:
                self.send(200, body, "image/svg+xml", "max-age=86400")
            else:
                self.send(404, b"no avatar", "text/plain")
        elif path.startswith("/vendor/"):
            body = vendor_file(path.removeprefix("/vendor/"))
            if body:
                self.send(200, body, "text/javascript; charset=utf-8", "max-age=604800")
            else:
                self.send(404, b"not available", "text/plain")
        elif path == "/favicon.ico":
            self.send(200, (HERE / "agent-office.ico").read_bytes(), "image/x-icon", "max-age=86400")
        elif path in ("/", "/index.html"):
            self.send(200, (HERE / "index.html").read_bytes(), "text/html; charset=utf-8")
        else:
            self.send(404, b"not found", "text/plain")


def running_instance(port: int) -> bool:
    opener = urllib.request.build_opener(urllib.request.ProxyHandler({}))
    try:
        with opener.open(f"http://127.0.0.1:{port}/api/ping", timeout=1) as res:
            return json.loads(res.read()).get("app") == "agent-office"
    except (OSError, ValueError):
        return False


def warm_up():
    """Price the transcripts and cache the first state before the browser asks for it."""
    try:
        refresh_pricing()
    except Exception:
        pass
    try:
        state_payload()
    except Exception:
        pass


def main():
    ports = [a for a in sys.argv[1:] if a.isdigit()]
    port = int(ports[0]) if ports else 8765
    if running_instance(port):
        # Already running (e.g. started from the desktop shortcut earlier): just show it.
        url = f"http://127.0.0.1:{port}/"
        print(f"Agent Office is already running: {url}", flush=True)
        if "--no-browser" not in sys.argv:
            webbrowser.open(url)
        return
    for candidate in range(port, port + 20):
        try:
            server = ThreadingHTTPServer(("127.0.0.1", candidate), Handler)
            break
        except OSError:
            continue
    else:
        raise SystemExit("사용할 수 있는 포트가 없습니다")
    url = f"http://127.0.0.1:{server.server_address[1]}/"
    print(f"Agent Office: {url}", flush=True)
    if "--no-browser" not in sys.argv:
        webbrowser.open(url)
    threading.Thread(target=warm_up, daemon=True).start()
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        pass
    finally:
        server.server_close()


if __name__ == "__main__":
    main()
