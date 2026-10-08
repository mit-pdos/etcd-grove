#!/usr/bin/env python3
"""The board: tasks (notes/tasks/<id>.md) and chat (notes/chat/<topic>.md).

See notes/collaboration.md. The board's source of truth is `origin/lean`. The commands
that change it (claim, release, block, ask, answer, review, done, drop, `new --push`,
and the `chat` commands) commit only the one file they change on top of `origin/lean`
and push it straight to `lean`, without touching the working tree; a push that loses a
race is retried against the new `origin/lean`, so two agents can never both claim one
task. Liveness of a claim is the newer of its `claimed-at` and the last commit pushed
to its branch (`task/<id>`): push the branch (`heartbeat`) at least every hour.

  etc/tasks.py next [--claim]       what to do now, in the "Go" order (AGENTS.md)
  etc/tasks.py wait [--interval S] [--timeout S]   block until `next` has something
  etc/tasks.py list [--all] [--state S]
  etc/tasks.py claim ID             then: git switch -c task/ID origin/lean
  etc/tasks.py heartbeat [ID]       push HEAD to task/ID (ID from the branch name)
  etc/tasks.py release ID [-m WHY]  give the task back (its branch is the handoff)
  etc/tasks.py block ID --on A,B [-m WHY]   depend on A, B and release
  etc/tasks.py ask ID -m QUESTION   state needs-human (a person answers with `answer`)
  etc/tasks.py answer ID -m ANSWER  (people) answer; the task is open again
  etc/tasks.py review ID | done ID | drop ID -m WHY
  etc/tasks.py new ID --title T --kind K [--priority N] [--design D] [--depends A,B] [--push]
  etc/tasks.py check [--rev REV]    validate the board (the working tree, or REV)
  etc/tasks.py status [--markdown]  summary: active work, questions, what is ready

  etc/tasks.py chat list [--all]    threads; which wait for an agent, which for a person
  etc/tasks.py chat new TOPIC --title T (-m TEXT | -F FILE) [--person]
  etc/tasks.py chat take TOPIC      an agent is replying (keeps other agents off it)
  etc/tasks.py chat post TOPIC (-m TEXT | -F FILE) [--person] [--resolve]
  etc/tasks.py chat resolve TOPIC | reopen TOPIC

The owner of a claim is `git config user.email` (or $ETCD_GROVE_OWNER): one person's
agents share it, which is how an agent resumes its person's unfinished work. A chat
message's author is `git config user.name`, tagged [agent] unless --person is given
(or $ETCD_GROVE_ROLE=person); a message people write by hand without a tag counts as
a person's.
"""
import argparse
import datetime as dt
import os
import re
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
TASKS = "notes/tasks"
CHAT = "notes/chat"
ROADMAP = "notes/roadmap.md"
MANUAL = "manual-notes.txt"
LEAN = "refs/remotes/origin/lean"

FIELDS = ["id", "title", "kind", "state", "priority", "design", "depends",
          "owner", "claimed-at", "implementer", "branch"]
REQUIRED = ["id", "title", "kind", "state", "priority"]
KINDS = ["proof", "spec", "translation", "framework", "design", "infra", "review", "fix-lean"]
STATES = ["open", "claimed", "review", "reviewing", "needs-human", "done", "dropped"]
OWNED = {"claimed", "reviewing"}          # states that need an owner
CLOSED = {"done", "dropped"}
ID_RE = re.compile(r"^[a-z0-9][a-z0-9._-]*$")

RESUME_IDLE = dt.timedelta(hours=2)     # own person's claim with no push for this long
STALE_IDLE = dt.timedelta(hours=24)     # anyone's claim with no push for this long


class Error(Exception):
    pass


# ---------------------------------------------------------------- git

def git(*args, input=None, env=None, check=True):
    p = subprocess.run(["git", *args], cwd=ROOT, input=input, env=env,
                       capture_output=True, text=True)
    if check and p.returncode != 0:
        raise Error(f"git {' '.join(args)}: {p.stderr.strip()}")
    return p


def fetch():
    git("fetch", "-q", "--prune", "origin",
        f"+refs/heads/lean:{LEAN}", "+refs/heads/task/*:refs/remotes/origin/task/*")


def me():
    who = os.environ.get("ETCD_GROVE_OWNER") or git("config", "user.email", check=False).stdout.strip()
    if not who:
        raise Error("no owner: set `git config user.email` (or $ETCD_GROVE_OWNER)")
    return who


def now():
    return dt.datetime.now(dt.timezone.utc).replace(second=0, microsecond=0)


def fmt_time(t):
    return t.strftime("%Y-%m-%dT%H:%MZ")


def parse_time(s):
    if not s:
        return None
    s = s.strip().replace("Z", "+00:00")
    try:
        t = dt.datetime.fromisoformat(s)
    except ValueError:
        return None
    return t if t.tzinfo else t.replace(tzinfo=dt.timezone.utc)


# ---------------------------------------------------------------- task files

class Task:
    def __init__(self, path, fields, body):
        self.path, self.f, self.body = path, fields, body

    def __getitem__(self, k):
        return self.f.get(k, "")

    def __setitem__(self, k, v):
        self.f[k] = v

    @property
    def id(self):
        return self["id"]

    @property
    def deps(self):
        return self.f.get("depends") or []

    @property
    def priority(self):
        try:
            return int(self["priority"])
        except ValueError:
            return 9

    def history(self, line):
        """Append a line to the `## History` section (kept last, written by tools only)."""
        entry = f"- {fmt_time(now())} {line}\n"
        if "\n## History\n" not in "\n" + self.body:
            self.body = self.body.rstrip("\n") + "\n\n## History\n"
        self.body = self.body.rstrip("\n") + "\n" + entry

    ORDER = FIELDS

    def text(self):
        out = ["---"]
        for k in self.ORDER + sorted(set(self.f) - set(self.ORDER)):
            if k not in self.f:
                continue
            v = self.f[k]
            if k == "depends":
                v = "[" + ", ".join(v) + "]"
            out.append(f"{k}: {v}".rstrip())
        return "\n".join(out) + "\n---\n" + self.body


def parse(path, text):
    if not text.startswith("---\n"):
        raise Error(f"{path}: no frontmatter (the file must start with `---`)")
    end = text.find("\n---\n", 4)
    if end < 0:
        raise Error(f"{path}: frontmatter not closed by `---`")
    fields = {}
    for n, line in enumerate(text[4:end].split("\n"), 2):
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        k, sep, v = line.partition(":")
        if not sep:
            raise Error(f"{path}:{n}: expected `key: value`")
        k, v = k.strip(), v.strip()
        if k == "depends":
            v = v.strip()
            if not (v.startswith("[") and v.endswith("]")):
                raise Error(f"{path}:{n}: depends must be a list, `[a, b]`")
            v = [d.strip() for d in v[1:-1].split(",") if d.strip()]
        fields[k] = v
    return Task(path, fields, text[end + 5:])


def blobs(rev, d):
    """[(path, text)] of the `*.md` files of directory d at rev (None: the working tree)."""
    if rev is None:
        full = os.path.join(ROOT, d)
        names = sorted(os.listdir(full)) if os.path.isdir(full) else []
        return [(f"{d}/{n}", open(os.path.join(full, n)).read()) for n in names if n.endswith(".md") and n != "README.md"]
    names = git("ls-tree", "--name-only", f"{rev}:{d}", check=False)
    if names.returncode != 0:
        return []
    paths = [f"{d}/{n}" for n in names.stdout.split() if n.endswith(".md") and n != "README.md"]
    if not paths:
        return []
    # One `cat-file --batch` for all files.
    p = subprocess.run(["git", "cat-file", "--batch"], cwd=ROOT, capture_output=True,
                       input="".join(f"{rev}:{x}\n" for x in paths).encode())
    data, out, i = p.stdout, [], 0
    for path in paths:
        header_end = data.index(b"\n", i)
        size = int(data[i:header_end].split()[2])
        out.append((path, data[header_end + 1: header_end + 1 + size].decode()))
        i = header_end + 1 + size + 1
    return out


def load_rev(rev):
    tasks = {}
    for path, text in blobs(rev, TASKS):
        t = parse(path, text)
        tasks[t.id or path] = t
    return tasks


def load_worktree():
    return load_rev(None)


def branch_times():
    out = git("for-each-ref", "--format=%(refname:strip=3) %(committerdate:iso-strict)",
              "refs/remotes/origin/task/").stdout
    times = {}
    for line in out.splitlines():
        name, _, t = line.partition(" ")
        times[name] = parse_time(t)
    return times


def last_activity(t, times):
    cands = [parse_time(t["claimed-at"]), times.get(t["branch"] or f"task/{t.id}")]
    cands = [c for c in cands if c]
    return max(cands) if cands else None


def idle(t, times):
    a = last_activity(t, times)
    return now() - a if a else dt.timedelta.max


def fmt_idle(d):
    if d == dt.timedelta.max:
        return "-"
    h = int(d.total_seconds() // 3600)
    return f"{h // 24}d{h % 24}h" if h >= 24 else f"{h}h{int(d.total_seconds() // 60) % 60:02d}m"


# ---------------------------------------------------------------- board logic

def validate(tasks):
    errs = []
    for key, t in tasks.items():
        p = t.path
        for k in REQUIRED:
            if not t[k]:
                errs.append(f"{p}: missing `{k}`")
        if t.id and os.path.basename(p) != f"{t.id}.md":
            errs.append(f"{p}: id `{t.id}` does not match the file name")
        if t.id and not ID_RE.match(t.id):
            errs.append(f"{p}: id must be lower-case letters, digits, `.`, `_`, `-`")
        if t["kind"] and t["kind"] not in KINDS:
            errs.append(f"{p}: kind `{t['kind']}` is not one of {', '.join(KINDS)}")
        if t["state"] and t["state"] not in STATES:
            errs.append(f"{p}: state `{t['state']}` is not one of {', '.join(STATES)}")
        if t["priority"] and t["priority"] not in ("1", "2", "3"):
            errs.append(f"{p}: priority must be 1, 2 or 3")
        if t["state"] in OWNED and not t["owner"]:
            errs.append(f"{p}: state `{t['state']}` needs an owner")
        if t["state"] in ("open", "review") and t["owner"]:
            errs.append(f"{p}: state `{t['state']}` has an owner (`{t['owner']}`)")
        if t["state"] in ("review", "reviewing") and not t["implementer"]:
            errs.append(f"{p}: state `{t['state']}` needs an implementer")
        if t["design"] and not os.path.exists(os.path.join(ROOT, t["design"])) and \
                git("cat-file", "-e", f"{LEAN}:{t['design']}", check=False).returncode != 0:
            errs.append(f"{p}: design `{t['design']}` does not exist")
        for d in t.deps:
            if d not in tasks:
                errs.append(f"{p}: depends on `{d}`, which is not a task")
            elif d == t.id:
                errs.append(f"{p}: depends on itself")
    # cycles
    state = {}

    def visit(k, stack):
        if state.get(k) == 2 or k not in tasks:
            return
        if state.get(k) == 1:
            errs.append("dependency cycle: " + " -> ".join(stack[stack.index(k):] + [k]))
            return
        state[k] = 1
        for d in tasks[k].deps:
            visit(d, stack + [k])
        state[k] = 2
    for k in tasks:
        visit(k, [])
    return errs


def deps_done(t, tasks):
    return all(d in tasks and tasks[d]["state"] == "done" for d in t.deps)


def unblocks(tasks):
    """Number of unfinished tasks that (transitively) wait on each task."""
    rev = {k: set() for k in tasks}
    for k, t in tasks.items():
        for d in t.deps:
            if d in rev:
                rev[d].add(k)
    memo = {}

    def down(k):
        if k not in memo:
            memo[k] = set()
            for j in rev[k]:
                if tasks[j]["state"] not in CLOSED:
                    memo[k] |= {j} | down(j)
        return memo[k]
    return {k: len(down(k)) for k in tasks}


def claimable(t, tasks, times, who):
    """Why `who` may claim t now (a string), or None."""
    s = t["state"]
    if s == "open":
        return "open, dependencies done" if deps_done(t, tasks) else None
    if s == "review" and not t["owner"]:
        return "review due" if t["implementer"] != who else None
    if s in OWNED:
        i = idle(t, times)
        if t["owner"] == who and i >= RESUME_IDLE:
            return f"your person's claim, idle {fmt_idle(i)}: resume it from its branch"
        if i >= STALE_IDLE:
            return f"stale claim of {t['owner']}, idle {fmt_idle(i)}: continue from its branch"
    return None


def lean_ci_failed():
    """The conclusion of the latest finished CI run on `lean` if it failed, else None.
    Needs `gh`; without it, None (the agent's own `lake build` is the check)."""
    try:
        p = subprocess.run(["gh", "run", "list", "--branch", "lean", "--workflow", "lean.yml",
                            "--status", "completed", "--limit", "1",
                            "--json", "conclusion,headSha,url",
                            "--template", "{{range .}}{{.conclusion}} {{.headSha}} {{.url}}{{end}}"],
                           cwd=ROOT, capture_output=True, text=True, timeout=30)
    except (OSError, subprocess.TimeoutExpired):
        return None
    parts = p.stdout.split()
    if p.returncode == 0 and parts and parts[0] not in ("success", "cancelled", "skipped"):
        return parts
    return None


def candidates(tasks, times, who):
    """Every task `who` could claim, in the "Go" order, as (rank, reason, task)."""
    ub = unblocks(tasks)
    out = []
    for t in tasks.values():
        why = claimable(t, tasks, times, who)
        if not why:
            continue
        s = t["state"]
        if t["kind"] == "fix-lean" and s == "open":
            rank = 1
        elif s in OWNED and t["owner"] == who:
            rank = 2
        elif s == "review":
            rank = 3
        elif s == "open":
            rank = 4
        else:
            rank = 5
        out.append(((rank, t.priority, -ub[t.id], t.id), why, t))
    out.sort(key=lambda x: x[0])
    return out


# ---------------------------------------------------------------- chat

# A thread is notes/chat/<topic>.md: frontmatter (title, status open|resolved, and
# `handler`/`handler-at` while an agent is replying), then messages, each headed
#     ### 2026-10-08T17:02Z · Alice Example [person]
# Messages are only ever appended (.gitattributes merges the files with `union`).
CHAT_ORDER = ["title", "status", "handler", "handler-at"]
CHAT_STATUS = ["open", "resolved"]
MSG_RE = re.compile(r"^### +(\S+).*? · +(.+?)(?: +\[(person|agent)\])? *$", re.M)
HANDLER_IDLE = dt.timedelta(hours=2)    # an agent's `take` without a reply for this long lapses


class Thread(Task):
    ORDER = CHAT_ORDER

    @property
    def topic(self):
        return os.path.basename(self.path)[:-3]

    def messages(self):
        """[(time, author, role)]; an untagged header is a person's (written by hand)."""
        return [(m.group(1), m.group(2), m.group(3) or "person") for m in MSG_RE.finditer(self.body)]

    def waiting_on(self):
        """`agent` if a person spoke last in an open thread, `person` if an agent did."""
        if self["status"] != "open":
            return None
        ms = self.messages()
        if not ms:
            return None
        return "agent" if ms[-1][2] == "person" else "person"

    def handled(self):
        t = parse_time(self["handler-at"])
        return bool(self["handler"]) and t is not None and now() - t < HANDLER_IDLE

    def append(self, author, role, text):
        self.body = (self.body.rstrip("\n") + f"\n\n### {fmt_time(now())} · {author} [{role}]\n\n"
                     + text.strip() + "\n")


def load_chats(rev):
    out = {}
    for path, text in blobs(rev, CHAT):
        t = parse(path, text)
        t.__class__ = Thread
        out[t.topic] = t
    return out


def author():
    name = git("config", "user.name", check=False).stdout.strip()
    return name or me()


def role(a):
    return "person" if getattr(a, "person", False) or os.environ.get("ETCD_GROVE_ROLE") == "person" else "agent"


def message_text(a):
    if getattr(a, "F", None):
        return open(a.F).read()
    if not a.m:
        raise Error("give the message with -m TEXT or -F FILE")
    return a.m


def change_thread(topic, fn, message):
    def update(_tasks):
        chats = load_chats(git("rev-parse", LEAN).stdout.strip())
        if topic not in chats:
            raise Error(f"no chat thread `{topic}` on origin/lean")
        t = chats[topic]
        fn(t)
        return {t.path: t.text()}
    return commit_on_lean(update, message)


def cmd_chat(a):
    c = a.chat
    if c == "list":
        if not a.no_fetch:
            fetch()
        chats = load_chats(LEAN)
        print(f"{'topic':36} {'status':9} {'waits on':9} {'last message':40} handler")
        for t in sorted(chats.values(), key=lambda t: (t["status"] != "open", t.topic)):
            if t["status"] != "open" and not a.all:
                continue
            ms = t.messages()
            last = f"{ms[-1][0]} {ms[-1][1]}" if ms else "-"
            h = t["handler"] if t.handled() else ""
            print(f"{t.topic:36} {t['status']:9} {t.waiting_on() or '-':9} {last[:40]:40} {h}")
        return
    if c == "new":
        if not ID_RE.match(a.topic):
            raise Error("topic must be lower-case letters, digits, `.`, `_`, `-`")
        path = f"{CHAT}/{a.topic}.md"
        t = Thread(path, {"title": a.title, "status": "open", "handler": "", "handler-at": ""},
                   f"\n# {a.title}\n")
        t.append(author(), role(a), message_text(a))

        def update(_tasks):
            if git("cat-file", "-e", f"{LEAN}:{path}", check=False).returncode == 0:
                raise Error(f"thread `{a.topic}` already exists: post to it")
            return {path: t.text()}
        commit_on_lean(update, f"chat: new {a.topic}")
        print(f"started {path}")
        return
    who = me()
    if c == "take":
        def fn(t):
            if t.waiting_on() != "agent":
                raise Error(f"`{t.topic}` is not waiting for an agent")
            if t.handled() and t["handler"] != who:
                raise Error(f"`{t.topic}` is being answered by {t['handler']}")
            t["handler"], t["handler-at"] = who, fmt_time(now())
        change_thread(a.topic, fn, f"chat: take {a.topic}")
        print(f"you are replying to {a.topic}: etc/tasks.py chat post {a.topic} -F reply.md")
    elif c == "post":
        text, r = message_text(a), role(a)

        def fn(t):
            if r == "agent" and t.handled() and t["handler"] != who:
                raise Error(f"`{t.topic}` is being answered by {t['handler']}")
            t.append(author(), r, text)
            if t["handler"] == who or r == "person":
                t["handler"] = t["handler-at"] = ""
            if a.resolve:
                t["status"] = "resolved"
        change_thread(a.topic, fn, f"chat: {a.topic}")
        print(f"posted to {a.topic}" + (" (resolved)" if a.resolve else ""))
    elif c in ("resolve", "reopen"):
        def fn(t):
            t["status"] = "resolved" if c == "resolve" else "open"
            t["handler"] = t["handler-at"] = ""
        change_thread(a.topic, fn, f"chat: {c} {a.topic}")
        print(f"{a.topic}: {'resolved' if c == 'resolve' else 'open'}")


def validate_chats(chats):
    errs = []
    for t in chats.values():
        if not ID_RE.match(t.topic):
            errs.append(f"{t.path}: topic (file name) must be lower-case letters, digits, `.`, `_`, `-`")
        if not t["title"]:
            errs.append(f"{t.path}: missing `title`")
        if t["status"] not in CHAT_STATUS:
            errs.append(f"{t.path}: status must be one of {', '.join(CHAT_STATUS)}")
    return errs


# ---------------------------------------------------------------- roadmap sync

def manual_blob(rev=LEAN):
    p = git("rev-parse", "-q", "--verify", f"{rev}:{MANUAL}", check=False)
    return p.stdout.strip()[:12] if p.returncode == 0 else None


def roadmap_synced(rev=LEAN):
    """The manual-notes.txt version notes/roadmap.md says it reflects (`manual-notes: <blob>`)."""
    p = git("show", f"{rev}:{ROADMAP}", check=False)
    if p.returncode != 0:
        return None
    m = re.search(r"^manual-notes:\s*([0-9a-f]+)", p.stdout, re.M)
    return m.group(1)[:12] if m else None


def sync_needed():
    """The id of the roadmap-sync task to create if manual-notes.txt changed since the
    roadmap was last brought in line with it, else None."""
    blob = manual_blob()
    if blob and roadmap_synced() != blob:
        return f"roadmap-sync-{blob[:8]}"
    return None


# ---------------------------------------------------------------- commits on lean

def commit_on_lean(update, message, tries=20):
    """Apply `update(tasks) -> {path: text}` to fresh `origin/lean` and push it to `lean`,
    retrying when another push wins the race. `update` raises Error to give up."""
    for _ in range(tries):
        fetch()
        base = git("rev-parse", LEAN).stdout.strip()
        changes = update(load_rev(base))
        with tempfile.TemporaryDirectory() as tmp:
            env = dict(os.environ, GIT_INDEX_FILE=os.path.join(tmp, "index"))
            git("read-tree", base, env=env)
            for path, text in changes.items():
                sha = git("hash-object", "-w", "--stdin", input=text).stdout.strip()
                git("update-index", "--add", "--cacheinfo", f"100644,{sha},{path}", env=env)
            tree = git("write-tree", env=env).stdout.strip()
        commit = git("commit-tree", tree, "-p", base, "-m", message).stdout.strip()
        p = git("push", "-q", "origin", f"{commit}:refs/heads/lean", check=False)
        if p.returncode == 0:
            git("update-ref", LEAN, commit)
            return commit
        if not re.search(r"rejected|fetch first|non-fast-forward|stale info", p.stderr):
            raise Error(f"push to lean failed: {p.stderr.strip()}")
    raise Error(f"lost the race to push to lean {tries} times; try again")


def change_task(tid, fn, message):
    """Run fn(task, tasks) on the fresh copy of task `tid`, then commit it on lean."""
    def update(tasks):
        if tid not in tasks:
            raise Error(f"no task `{tid}` on origin/lean")
        t = tasks[tid]
        fn(t, tasks)
        return {t.path: t.text()}
    return commit_on_lean(update, message)


# ---------------------------------------------------------------- commands

TEMPLATE = """
# {title}

## Goal

What is true when this is done, in terms of files and theorems.

## Context

Pointers: the design doc section, the Go source (file:line at the pinned fork), the
callees' specs, related tasks.

## Log

Dated entries by whoever works on it: what was done, where it stopped, dead ends.
"""


def cmd_new(a):
    if not ID_RE.match(a.id):
        raise Error("id must be lower-case letters, digits, `.`, `_`, `-`")
    if a.kind not in KINDS:
        raise Error(f"kind must be one of {', '.join(KINDS)}")
    path = f"{TASKS}/{a.id}.md"
    t = Task(path, {"id": a.id, "title": a.title, "kind": a.kind, "state": "open",
                    "priority": str(a.priority), "design": a.design or "",
                    "depends": [d.strip() for d in (a.depends or "").split(",") if d.strip()],
                    "owner": "", "claimed-at": "", "implementer": "", "branch": ""},
             TEMPLATE.format(title=a.title))
    t.history(f"created by {me()}")
    if a.push:
        def update(tasks):
            if a.id in tasks:
                raise Error(f"task `{a.id}` already exists on origin/lean")
            return {path: t.text()}
        commit_on_lean(update, f"task: new {a.id}")
        print(f"created {path} on lean")
    else:
        full = os.path.join(ROOT, path)
        if os.path.exists(full):
            raise Error(f"{path} already exists")
        os.makedirs(os.path.dirname(full), exist_ok=True)
        with open(full, "w") as f:
            f.write(t.text())
        print(f"wrote {path} (fill in Goal and Context; it is claimable once it lands)")


def cmd_claim(a):
    who = me()

    def fn(t, tasks):
        why = claimable(t, tasks, branch_times(), who)
        if not why:
            raise Error(f"`{t.id}` is not claimable: state {t['state']}"
                        + (f", owner {t['owner']}" if t["owner"] else "")
                        + ("" if deps_done(t, tasks) else
                           f", waiting on {[d for d in t.deps if tasks.get(d) and tasks[d]['state'] != 'done']}"))
        prev = t["owner"]
        if t["state"] == "open":
            t["state"] = "claimed"
        elif t["state"] == "review":
            t["state"] = "reviewing"
        t["owner"], t["claimed-at"] = who, fmt_time(now())
        t["branch"] = t["branch"] or f"task/{t.id}"
        t.history(f"claimed by {who} ({t['state']})" + (f", taken over from {prev}" if prev and prev != who else ""))
    change_task(a.id, fn, f"claim: {a.id}")
    t = load_rev(LEAN)[a.id]
    print(f"claimed {a.id} ({t['state']})")
    br = t["branch"]
    if git("rev-parse", "-q", "--verify", f"refs/remotes/origin/{br}", check=False).returncode == 0:
        print(f"its branch exists: git switch -c {br} origin/{br} && git rebase origin/lean")
    else:
        print(f"start it:          git switch -c {br} origin/lean")
    print(f"push it at least hourly: etc/tasks.py heartbeat   land it: etc/land.py")
    return t


def people_first(tasks):
    """What people are waiting on, before any task: (kind, name, text) or None.
    kind is `new-task` (create and claim it), `chat` (take the thread and reply)."""
    failed = lean_ci_failed()
    if failed and not any(t["kind"] == "fix-lean" and t["state"] not in CLOSED for t in tasks.values()):
        tid = f"fix-lean-{failed[1][:9]}"
        return ("new-task", tid, dict(kind="fix-lean", priority=1, title=f"Fix lean (CI {failed[0]} at {failed[1][:9]})"),
                f"lean is broken: CI {failed[0]} at {failed[1][:9]} ({failed[2]})")
    for t in sorted(load_chats(LEAN).values(), key=lambda t: t.messages()[-1][0] if t.messages() else ""):
        if t.waiting_on() == "agent" and not t.handled():
            ms = t.messages()
            return ("chat", t.topic, None,
                    f"a person wrote in chat `{t.topic}` ({ms[-1][0]}, {ms[-1][1]}): read "
                    f"{CHAT}/{t.topic}.md and reply (or turn it into tasks and say so in the thread)")
    sync = sync_needed()
    if sync and sync not in tasks:
        return ("new-task", sync, dict(kind="design", priority=1,
                                       title=f"Bring notes/roadmap.md in line with manual-notes.txt ({manual_blob()[:8]})"),
                f"{MANUAL} changed since {ROADMAP} last reflected it")
    return None


def cmd_next(a):
    who = me()
    if not a.no_fetch:
        fetch()
    for tries in range(5):
        tasks = load_rev(LEAN)
        pf = people_first(tasks)
        if pf:
            kind, name, new, why = pf
            if not a.claim:
                print(f"{name}: {why}")
                return pf
            try:
                if kind == "chat":
                    a.chat, a.topic = "take", name
                    cmd_chat(a)
                else:
                    cmd_new(argparse.Namespace(id=name, design=None, depends=None, push=True, **new))
                    a.id = name
                    cmd_claim(a)
                return pf
            except Error as e:
                print(f"{name}: {e}; trying the next thing", file=sys.stderr)
                fetch()
                continue
        cands = candidates(tasks, branch_times(), who)
        if not cands:
            print("nothing to do: plan, or wait. If a direction in manual-notes.txt or "
                  "notes/roadmap.md has no design doc and no design task, create one "
                  "(etc/tasks.py new … --kind design --push), claim it, and write "
                  "notes/design/<topic>.md and the tasks it breaks into. Otherwise run "
                  "etc/tasks.py wait.")
            return None
        _, why, t = cands[0]
        if not a.claim:
            print(f"{t.id}: {t['title']}\n  {why}  (priority {t['priority']}, kind {t['kind']})")
            for _, why2, t2 in cands[1:4]:
                print(f"  then: {t2.id} ({why2})")
            return t
        try:
            a.id = t.id
            cmd_claim(a)
            return t
        except Error as e:
            print(f"{t.id}: {e}; trying the next one", file=sys.stderr)
            fetch()
    raise Error("could not claim anything after 5 tries")


def cmd_wait(a):
    """Poll origin until there is something to do (for an idle agent on a VM)."""
    import time
    who, start = me(), time.time()
    while True:
        fetch()
        tasks = load_rev(LEAN)
        pf = people_first(tasks)
        cands = candidates(tasks, branch_times(), who)
        if pf or cands:
            print(pf[3] if pf else f"{cands[0][2].id}: {cands[0][1]}")
            print("run: etc/tasks.py next --claim")
            return
        if a.timeout and time.time() - start >= a.timeout:
            print("nothing to do yet (timed out)")
            sys.exit(2)
        time.sleep(a.interval)


def cmd_heartbeat(a):
    tid = a.id or current_task()
    if not tid:
        raise Error("not on a task/<id> branch: give the task id")
    br = f"task/{tid}"
    fetch()
    remote = git("rev-parse", "-q", "--verify", f"refs/remotes/origin/{br}", check=False).stdout.strip()
    head = git("rev-parse", "HEAD").stdout.strip()
    if remote == head:
        # Nothing new to push: an empty commit (etc/land.py drops it when rebasing).
        git("commit", "-q", "--allow-empty", "-m", f"heartbeat: {tid}")
    push_task_branch(br, remote)
    print(f"pushed HEAD to {br}")


def push_task_branch(br, expected=None):
    """Push HEAD to the task branch. etc/land.py rebases it, so this may rewrite it: only
    over the tip last fetched (`expected`), never over someone else's newer push."""
    if expected is None:
        expected = git("rev-parse", "-q", "--verify", f"refs/remotes/origin/{br}", check=False).stdout.strip()
    git("push", "-q", f"--force-with-lease=refs/heads/{br}:{expected}", "origin", f"HEAD:refs/heads/{br}")


def current_task():
    b = git("branch", "--show-current", check=False).stdout.strip()
    return b[len("task/"):] if b.startswith("task/") else None


def need_owner(t, who, force):
    if t["owner"] != who and not force:
        raise Error(f"`{t.id}` is owned by `{t['owner'] or 'nobody'}`, not you (--force to override)")


def unclaim(t):
    t["state"] = {"claimed": "open", "reviewing": "review"}.get(t["state"], t["state"])
    t["owner"] = t["claimed-at"] = ""


def cmd_release(a):
    who = me()

    def fn(t, tasks):
        need_owner(t, who, a.force)
        unclaim(t)
        t.history(f"released by {who}" + (f": {a.m}" if a.m else ""))
    change_task(a.id, fn, f"release: {a.id}")
    print(f"released {a.id}")


def cmd_block(a):
    who = me()
    on = [d.strip() for d in a.on.split(",") if d.strip()]

    def fn(t, tasks):
        need_owner(t, who, a.force)
        missing = [d for d in on if d not in tasks]
        if missing:
            raise Error(f"no such tasks on origin/lean: {missing} (create them first: new … --push)")
        t["depends"] = t.deps + [d for d in on if d not in t.deps]
        unclaim(t)
        t.history(f"blocked by {who} on {', '.join(on)}" + (f": {a.m}" if a.m else ""))
    change_task(a.id, fn, f"block: {a.id} on {', '.join(on)}")
    print(f"{a.id} now waits on {', '.join(on)} (released)")


def cmd_ask(a):
    who = me()

    def fn(t, tasks):
        t["state"] = "needs-human"
        t["owner"] = t["owner"] or who
        t.history(f"QUESTION from {who}: {a.m}")
    change_task(a.id, fn, f"ask: {a.id}")
    print(f"{a.id} is waiting for a person (etc/tasks.py status lists the questions)")


def cmd_answer(a):
    who = me()

    def fn(t, tasks):
        if t["state"] != "needs-human":
            raise Error(f"`{t.id}` is not waiting for a person (state {t['state']})")
        # Open again, for any agent; its branch (kept) holds the work so far.
        t["state"] = "open"
        t["owner"] = t["claimed-at"] = ""
        t.history(f"ANSWER from {who}: {a.m}")
    change_task(a.id, fn, f"answer: {a.id}")
    print(f"answered {a.id}")


def set_state(tid, state, note="", force=False):
    who = me()

    def fn(t, tasks):
        if t["state"] in OWNED or t["state"] == "needs-human":
            need_owner(t, who, force)
        if state == "review":
            t["implementer"] = t["owner"] or who
        t["state"] = state
        t["owner"] = t["claimed-at"] = ""
        t.history(f"{state} ({who})" + (f": {note}" if note else ""))
    change_task(tid, fn, f"{state}: {tid}")
    print(f"{tid}: {state}")


def cmd_list(a):
    if not a.no_fetch:
        fetch()
    tasks, times = load_rev(LEAN), branch_times()
    rows = [t for t in tasks.values()
            if (a.all or t["state"] not in CLOSED) and (not a.state or t["state"] in a.state)]
    rows.sort(key=lambda t: (STATES.index(t["state"]) if t["state"] in STATES else 9, t.priority, t.id))
    print(f"{'id':40} {'state':12} p {'kind':11} {'owner':28} idle")
    for t in rows:
        state = t["state"] + ("*" if t["state"] == "open" and not deps_done(t, tasks) else "")
        i = fmt_idle(idle(t, times)) if t["state"] in OWNED else ""
        print(f"{t.id:40} {state:12} {t['priority']:1} {t['kind']:11} {t['owner']:28} {i}")
    print("(* waiting on dependencies)")


def cmd_check(a):
    tasks = load_rev(a.rev) if a.rev else load_worktree()
    chats = load_chats(a.rev)
    errs = validate(tasks) + validate_chats(chats)
    for e in errs:
        print(e, file=sys.stderr)
    if errs:
        sys.exit(1)
    print(f"{len(tasks)} tasks, {len(chats)} chat threads, no errors")


def cmd_status(a):
    if not a.no_fetch:
        fetch()
    tasks, times = load_rev(LEAN), branch_times()
    md = a.markdown
    h = (lambda s: f"\n## {s}\n") if md else (lambda s: f"\n{s}:")
    counts = {s: sum(t["state"] == s for t in tasks.values()) for s in STATES}
    print(("# Task board\n\n" if md else "") +
          (", ".join(f"{n} {s}" for s, n in counts.items() if n) or "no tasks"))
    chats = load_chats(LEAN)
    for side, head in (("person", "Chat waiting for people"), ("agent", "Chat waiting for an agent")):
        ts = [t for t in chats.values() if t.waiting_on() == side]
        if ts:
            print(h(head))
            for t in sorted(ts, key=lambda t: t.topic):
                ms = t.messages()
                extra = f", {t['handler']} replying" if side == "agent" and t.handled() else ""
                print(f"- `{CHAT}/{t.topic}.md`: {t['title']} (last: {ms[-1][0]}, {ms[-1][1]}{extra})")
    sync = sync_needed()
    if sync:
        print(h("Roadmap"))
        print(f"{MANUAL} changed since {ROADMAP} last reflected it (task `{sync}`)")
    act = [t for t in tasks.values() if t["state"] in OWNED]
    if act:
        print(h("In progress"))
        for t in sorted(act, key=lambda t: t.id):
            print(f"- `{t.id}` ({t['state']}) {t['owner']}, idle {fmt_idle(idle(t, times))}: {t['title']}")
    q = [t for t in tasks.values() if t["state"] == "needs-human"]
    if q:
        print(h("Waiting for a person"))
        for t in sorted(q, key=lambda t: t.id):
            asked = [l for l in t.body.splitlines() if "QUESTION from" in l]
            print(f"- `{t.id}`: {asked[-1][2:] if asked else t['title']}")
    ready = [c for c in candidates(tasks, times, "") if c[2]["state"] in ("open", "review")]
    if ready:
        print(h("Ready to claim"))
        for _, why, t in ready[:15]:
            print(f"- `{t.id}` (p{t['priority']}, {t['kind']}): {t['title']}")
    waiting = [t for t in tasks.values() if t["state"] == "open" and not deps_done(t, tasks)]
    if waiting:
        print(h("Waiting on dependencies"))
        for t in sorted(waiting, key=lambda t: t.id):
            pend = [d for d in t.deps if not (d in tasks and tasks[d]["state"] == "done")]
            print(f"- `{t.id}` waits on {', '.join(f'`{d}`' for d in pend)}")


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0],
                                 formatter_class=argparse.RawDescriptionHelpFormatter, epilog=__doc__)
    sub = ap.add_subparsers(dest="cmd", required=True)
    p = sub.add_parser("next"); p.add_argument("--claim", action="store_true"); p.add_argument("--no-fetch", action="store_true")
    p = sub.add_parser("list"); p.add_argument("--all", action="store_true"); p.add_argument("--state", action="append"); p.add_argument("--no-fetch", action="store_true")
    p = sub.add_parser("claim"); p.add_argument("id")
    p = sub.add_parser("heartbeat"); p.add_argument("id", nargs="?")
    for c in ("release", "block", "ask", "answer", "review", "done", "drop"):
        p = sub.add_parser(c); p.add_argument("id"); p.add_argument("-m", default="", required=c in ("ask", "answer", "drop"))
        p.add_argument("--force", action="store_true")
        if c == "block":
            p.add_argument("--on", required=True)
    p = sub.add_parser("new"); p.add_argument("id"); p.add_argument("--title", required=True)
    p.add_argument("--kind", required=True); p.add_argument("--priority", type=int, default=3, choices=[1, 2, 3])
    p.add_argument("--design"); p.add_argument("--depends"); p.add_argument("--push", action="store_true")
    p = sub.add_parser("check"); p.add_argument("--rev")
    p = sub.add_parser("status"); p.add_argument("--markdown", action="store_true"); p.add_argument("--no-fetch", action="store_true")
    p = sub.add_parser("wait"); p.add_argument("--interval", type=int, default=300); p.add_argument("--timeout", type=int, default=0)
    p = sub.add_parser("chat"); cs = p.add_subparsers(dest="chat", required=True)
    q = cs.add_parser("list"); q.add_argument("--all", action="store_true"); q.add_argument("--no-fetch", action="store_true")
    q = cs.add_parser("new"); q.add_argument("topic"); q.add_argument("--title", required=True)
    q.add_argument("-m"); q.add_argument("-F"); q.add_argument("--person", action="store_true")
    q = cs.add_parser("post"); q.add_argument("topic"); q.add_argument("-m"); q.add_argument("-F")
    q.add_argument("--person", action="store_true"); q.add_argument("--resolve", action="store_true")
    for c in ("take", "resolve", "reopen"):
        q = cs.add_parser(c); q.add_argument("topic")
    a = ap.parse_args()
    try:
        {"next": cmd_next, "list": cmd_list, "claim": cmd_claim, "heartbeat": cmd_heartbeat,
         "release": cmd_release, "block": cmd_block, "ask": cmd_ask, "answer": cmd_answer,
         "review": lambda a: set_state(a.id, "review", a.m, a.force),
         "done": lambda a: set_state(a.id, "done", a.m, a.force),
         "drop": lambda a: set_state(a.id, "dropped", a.m, a.force),
         "new": cmd_new, "check": cmd_check, "status": cmd_status,
         "wait": cmd_wait, "chat": cmd_chat}[a.cmd](a)
    except Error as e:
        sys.exit(f"etc/tasks.py: {e}")


if __name__ == "__main__":
    main()
