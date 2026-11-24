#!/usr/bin/env python3
"""gh-inbox: the shared GitHub coordination tool of the sessions working on mit-pdos/etcd-grove,
mit-pdos/perennial and mit-pdos/dsverify-lab. The convention it reads: notes/coordination.md.

    gh-inbox.py watch --me H [--interval 2m] [--backlog 2h] [--remind 6h] [--once | --until-event]
    gh-inbox.py open [--for H] [--by H] [--closed]   open and acked items, with owner and age
    gh-inbox.py digest --for upamanyus               what is waiting on a person
    gh-inbox.py post --me H --to H... --issue N [--repo R] [--ask [TEXT]] FILE
                                                     writes FILE with its to:/from: lines added,
                                                     and prints the `gh api ... -F body=@...` to run
    gh-inbox.py scan --since DATE [--dry-run]        legacy posts that look like open asks
    gh-inbox.py show ID                              one item's history

The tool only reads GitHub: it never posts, edits or closes anything. Every item's state is
derived from the threads and the open pull requests alone, so every session and machine computes
the same answer; ~/.cache/gh-inbox/<handle>/ caches the API responses (with their ETags), the
cursor, and what `watch` has printed. The token comes from GH_TOKEN and is never written or
printed. Python 3 standard library only.
"""
import argparse, datetime, hashlib, json, os, re, shlex, sys, time
import urllib.error, urllib.parse, urllib.request

OWNER = "mit-pdos"
REPOS = ["etcd-grove", "perennial", "dsverify-lab"]
API = "https://api.github.com"
HERE = os.path.dirname(os.path.abspath(__file__))
REGISTRY = os.path.join(HERE, "sessions.txt")
UTC = datetime.timezone.utc


def now_utc():
    return datetime.datetime.now(UTC)


def ts(s):
    return datetime.datetime.strptime(s, "%Y-%m-%dT%H:%M:%SZ").replace(tzinfo=UTC)


def iso(d):
    return d.astimezone(UTC).strftime("%Y-%m-%dT%H:%M:%SZ")


def age(created, now):
    s = max(0, int((now - ts(created)).total_seconds()))
    d, h, m = s // 86400, s % 86400 // 3600, s % 3600 // 60
    return f"{d}d{h}h" if d else f"{h}h{m:02d}m" if h else f"{m}m"


def duration(s):
    m = re.fullmatch(r"(\d+)([smhd]?)", s.strip())
    if not m:
        raise argparse.ArgumentTypeError(f"not a duration: {s!r} (e.g. 90s, 30m, 6h, 2d)")
    return int(m[1]) * {"": 1, "s": 1, "m": 60, "h": 3600, "d": 86400}[m[2]]


def short_repo(r):
    return r.split("/")[-1]


def word_re(s):
    return rf"(?<![\w-]){re.escape(s)}(?![\w-])"


# ---------------------------------------------------------------- the registry (etc/sessions.txt)

class Session:
    def __init__(self, handle, owner, machine, account, claims, sigs, aliases):
        self.handle, self.owner, self.machine, self.account = handle, owner, machine, account
        self.claims, self.sigs, self.aliases = claims, sigs, aliases

    @property
    def human(self):
        return "human" in self.claims


class Registry:
    """`handle | owner | machine | account | claims | legacy signatures | legacy aliases`, one
    session per line (etc/sessions.txt says what each field means)."""

    def __init__(self, sessions):
        self.sessions = {s.handle.lower(): s for s in sessions}

    @classmethod
    def load(cls, path=REGISTRY):
        with open(path) as f:
            return cls.parse(f.read())

    @classmethod
    def parse(cls, text):
        out = []
        for ln in text.splitlines():
            if not ln.strip() or ln.lstrip().startswith("#"):
                continue
            f = [x.strip() for x in re.split(r"(?<!\|)\|(?!\|)", ln)] + [""] * 7
            many = lambda v: [x.strip() for x in v.split("||") if x.strip()]
            claims = [c.strip() for c in f[4].split(",") if c.strip()]
            out.append(Session(f[0], f[1], f[2], f[3], claims, many(f[5]), many(f[6])))
        return cls(out)

    def get(self, h):
        return self.sessions.get((h or "").lower())

    def canon(self, h):
        s = self.get(h)
        return s.handle if s else ("all" if (h or "").lower() == "all" else h)

    def known(self, h):
        return (h or "").lower() == "all" or self.get(h) is not None

    def human_by_login(self, login):
        for s in self.sessions.values():
            if s.human and s.account == login:
                return s.handle
        return None

    def owner_accounts(self, owner):
        return {s.account for s in self.sessions.values() if s.owner == owner} | {owner}

    def queue_handles(self):
        return [s.handle for s in self.sessions.values() if "queue" in s.claims]

    def queue_accounts(self):
        return {s.account for s in self.sessions.values() if "queue" in s.claims}

    def landers(self, repo):
        return [s.handle for s in self.sessions.values() if f"lands:{short_repo(repo)}" in s.claims]

    def reviewer_handles(self, login):
        h = self.human_by_login(login)
        if h:
            return [h]
        hs = [s.handle for s in self.sessions.values() if s.account == login]
        rv = [x for x in hs if "reviews" in self.get(x).claims]
        return rv or ["@" + login]

    def sig_author(self, body):
        """The session whose legacy signature ends the post (in its last three non-empty lines)."""
        tail = "\n".join([l for l in visible_lines(body) if l.strip()][-3:])
        best = None
        for s in self.sessions.values():
            for sig in s.sigs:
                if sig in tail and (best is None or len(sig) > len(best[1])):
                    best = (s.handle, sig)
        return best[0] if best else None


# ---------------------------------------------------------------- parsing a post

FENCE = re.compile(r"^\s*(```|~~~)")
KEYS = "ask|decision|re|ack|done|declined|superseded-by"
LINE = re.compile(rf"^\s*(?:[-*]\s+)?(?:\*\*)?({KEYS})(?:\*\*)?:(?:\*\*)?\s*(.*)$")
VERB = re.compile(r"^(done|declined|ack|superseded-by):\s*(.*)$")
QUEUE = re.compile(r"^\s*land-queue:\s+(\S+)\s+([0-9a-f]{7,40})\s*$", re.M)
VMBUILD = re.compile(r"^\s*vm-build:\s+(\S+)\s+([0-9a-f]{7,40})\s+(.+)$", re.M)
TAGS = re.compile(r"</?sub>|</?sup>")


def visible_lines(body):
    """The lines of a post outside code fences and block quotes."""
    out, fence = [], False
    for ln in (body or "").splitlines():
        if FENCE.match(ln):
            fence = not fence
            continue
        if not fence and not ln.lstrip().startswith(">"):
            out.append(ln)
    return out


def norm_id(t):
    """An item id, from an id or a link to a comment, an issue or a PR; None if `t` is none."""
    m = re.search(r"github\.com/[\w.-]+/([\w.-]+)/(?:issues|pull)/(\d+)(?:#issuecomment-(\d+))?", t)
    if m:
        return m[3] or f"{m[1]}#{m[2]}"
    m = re.fullmatch(r"(?:issuecomment-)?(\d{6,}(?:\.\d+)?)", t)
    if m:
        return m[1]
    if re.fullmatch(r"(?:queue|vm-build|land|review):\S+", t) or re.fullmatch(r"[\w.-]+#\d+", t):
        return t
    return None


def take_ids(val):
    """The item ids at the start of `val`, and the rest of it."""
    ids, toks = [], val.strip().split()
    i = 0
    while i < len(toks):
        n = norm_id(toks[i].strip().rstrip(",;.:)").lstrip("("))
        if n is None:
            break
        ids.append(n)
        i += 1
    return ids, " ".join(toks[i:])


class Post:
    def __init__(self, d):
        self.id, self.repo, self.number = d["id"], d["repo"], d["number"]
        self.kind, self.login, self.url, self.title = d["kind"], d["login"], d["url"], d.get("title", "")
        self.created, self.updated, self.body = d["created"], d["updated"], d.get("body") or ""
        lines = visible_lines(self.body)
        nonempty = [l for l in lines if l.strip()]
        self.to = None
        if nonempty and re.match(r"^\s*to:", nonempty[0]):
            v = re.sub(r"\([^)]*\)", " ", nonempty[0].split(":", 1)[1])
            self.to = [t for t in re.split(r"[,\s]+", v) if t and not t.startswith("@")]
        self.frm = None
        if nonempty:
            last = TAGS.sub("", nonempty[-1]).strip().lstrip("—–- ").strip()
            m = re.match(r"^from:\s*(\S+)", last)
            if m:
                self.frm = m[1].rstrip(".,")
        self.lines = [(m[1], m[2].strip()) for m in map(LINE.match, lines) if m]
        self.convention = self.to is not None or self.frm is not None or bool(self.lines)
        text = "\n".join(lines)
        self.queue = QUEUE.findall(text)
        self.vmbuild = VMBUILD.findall(text)

    def where(self):
        return f"{self.repo}#{self.number}"

    def summary(self, n=220):
        body = "\n".join(l for l in self.body.splitlines()
                         if not re.match(r"^\s*(to|from):", TAGS.sub("", l).strip().lstrip("—- ")))
        s = re.sub(r"\s+", " ", (self.title + ": " if self.title else "") + body).strip()
        return s[:n] + ("…" if len(s) > n else "")

    def actions(self):
        """(verb, targets, text, new ids) for each acking or closing line. A `re:` line names the
        targets of the post's lines without ids; a `re:` with no verb at all is a reply (an ack)."""
        re_ids, out, deferred, covered = [], [], [], set()
        for key, val in self.lines:
            if key == "re":
                ids, rest = take_ids(val)
                re_ids += ids
                m = VERB.match(rest)
                if m:
                    if m[1] == "superseded-by":
                        new, why = take_ids(m[2])
                        out.append(("superseded", ids, why, new))
                    else:
                        out.append((m[1], ids, m[2], []))
                    covered.update(ids)
            elif key in ("done", "declined", "ack", "superseded-by"):
                ids, rest = take_ids(val)
                if key == "superseded-by":
                    deferred.append(("superseded", rest, ids))
                elif ids:
                    out.append((key, ids, rest, []))
                    covered.update(ids)
                else:
                    deferred.append((key, rest, []))
        for verb, rest, new in deferred:
            out.append((verb, list(re_ids), rest, new))
            covered.update(re_ids)
        out += [("reply", [i], "", []) for i in re_ids if i not in covered]
        return out


# ---------------------------------------------------------------- deriving the items

class Item:
    def __init__(self, id, kind, to, asker, created, url, where, text):
        self.id, self.kind, self.to, self.asker = id, kind, list(to), asker
        self.created, self.url, self.where, self.text = created, url, where, text
        self.state, self.owner, self.closed_by, self.how, self.superseded_by = "open", None, None, None, []
        self.updated, self.history = None, [(created, asker, "opened", url)]

    def line(self, now):
        who = f" owner {self.owner}" if self.state == "acked" else ""
        end = f" ({self.how} by {self.closed_by})" if self.state == "closed" else ""
        return (f"{self.id} [{self.state}{end}] {self.kind} to {','.join(self.to)}{who} from {self.asker}"
                f" age {age(self.created, now)} {self.where}: {self.text} <{self.url}>")


class Model:
    """Every item and its state, computed from the posts and the open pull requests alone."""

    def __init__(self, reg, posts, pulls):
        self.reg = reg
        self.posts = sorted((Post(p) for p in posts), key=lambda p: (p.created, p.id))
        self.pulls = pulls
        self.items, self.author, self.queue_posts = {}, {}, set()
        self._derive()

    def who(self, p):
        if p.frm:
            return self.reg.canon(p.frm)
        return self.reg.sig_author(p.body) or self.reg.human_by_login(p.login) or "@" + p.login

    def _new(self, it):
        old = self.items.get(it.id)
        if old:   # the id is reused once the old item is closed: keep the old one under its date
            old.id, old.archived = f"{old.id}@{old.created}", True
            self.items[old.id] = old
        self.items[it.id] = it
        return it

    def _derive(self):
        for pr in self.pulls:
            self._pr_items(pr)
        qacc = self.reg.queue_accounts()
        for p in self.posts:
            a = self.author[p.id] = self.who(p)
            asks = [(k, v) for k, v in p.lines if k in ("ask", "decision")]
            for n, (k, v) in enumerate(asks):
                to = [self.reg.canon(t) for t in (p.to or ["all"])]
                self._new(Item(p.id if n == 0 else f"{p.id}.{n + 1}", k, to, a, p.created, p.url,
                               p.where(), v))
            for b, sha in p.queue:
                self._land_request(b, sha, a, p)
            for b, sha, cmd in p.vmbuild:
                iid, n = f"vm-build:{b}@{sha[:10]}", 1
                while iid in self.items and self.items[iid].state != "closed":   # several on one head
                    n += 1
                    iid = f"vm-build:{b}@{sha[:10]}.{n}"
                self._new(Item(iid, "vm-build", self.reg.queue_handles() or ["all"],
                               a, p.created, p.url, p.where(), f"vm-build: {b} {sha[:10]} {cmd.strip()[:80]}"))
            if p.login in qacc or "queue" in getattr(self.reg.get(a), "claims", []):
                self._queue_result(p, a)
            for verb, targets, text, new in p.actions():
                if verb == "superseded" and not new and asks:   # superseded by this post's ask
                    new = [p.id]
                for t in targets:
                    for it in self._resolve(t):
                        self._act(it, verb, a, p, text, new)

    def _pr_items(self, pr):
        repo, n = pr["repo"], pr["number"]
        where = f"{repo}#{n}"
        landers = [h for h in self.reg.landers(repo)
                   if pr["login"] not in self.reg.owner_accounts(self.reg.get(h).owner)]
        if landers and not pr.get("draft") and not pr["login"].endswith("[bot]"):
            it = Item(f"land:{where}", "land", landers, "@" + pr["login"], pr["created"], pr["url"],
                      where, pr["title"])
            it.updated = pr["updated"]
            self._new(it)
        for login in pr.get("reviewers", []):
            self._new(Item(f"review:{where}:{login}", "review", self.reg.reviewer_handles(login),
                           "@" + pr["login"], pr["created"], pr["url"], where, pr["title"]))

    def _resolve(self, t):
        if t in self.items:
            return [self.items[t]]
        if re.fullmatch(r"\d+", t):   # a comment id names all of that comment's items
            return [i for k, i in self.items.items() if k.startswith(t + ".")]
        if re.fullmatch(r"[\w.-]+#\d+", t):   # a PR, by number or link
            return [i for k, i in self.items.items() if k == f"land:{t}" or k.startswith(f"review:{t}:")]
        return []

    def may_act(self, it, who):
        if who == it.asker or who in it.to or ("all" in it.to and not who.startswith("@")):
            return True
        s = self.reg.get(who)   # a session acts for its owner when the owner is addressed
        if s and s.owner in it.to:
            return True
        return any(t.startswith("@") and s and s.account == t[1:] for t in it.to)

    def _act(self, it, verb, who, p, text, new):
        if it.state == "closed":
            it.history.append((p.created, who, f"{verb} (already closed)", p.url))
            return
        if not self.may_act(it, who):
            it.history.append((p.created, who, f"{verb} ignored: not an addressee or the asker", p.url))
            return
        it.history.append((p.created, who, verb + (": " + text if text else ""), p.url))
        if verb in ("ack", "reply"):
            it.state, it.owner = "acked", who
            return
        it.state, it.closed_by = "closed", who
        if verb == "superseded":
            it.how, it.superseded_by = "superseded", new
        elif who == it.asker and who not in it.to:
            it.how = "withdrawn"
        else:
            it.how = verb

    # ----- the land queue and the VM: their lines and result posts are only read, never written

    def _land_request(self, b, sha, a, p):
        iid = f"queue:{b}"
        it = self.items.get(iid)
        to = self.reg.queue_handles() or ["all"]
        if it and it.state != "closed":   # re-sent after a failure, or a new head
            it.to, it.state, it.owner, it.asker = to, "open", None, a
            it.text, it.url = f"land-queue: {b} {sha}", p.url
            it.history.append((p.created, a, f"re-sent at {sha}", p.url))
        else:
            self._new(Item(iid, "land-queue", to, a, p.created, p.url, p.where(), f"land-queue: {b} {sha}"))

    def _branch(self, b, kind):
        """The queue or VM item a backquoted name in a result post means (by name, or its name
        before `/`)."""
        prefix = "vm-build:" if kind == "vm" else "queue:"
        names = [k[len(prefix):] for k, i in self.items.items()
                 if k.startswith(prefix) and not getattr(i, "archived", False)]
        flat = lambda x: x.replace("/", "_")   # the queue names its files with `/` as `_`
        if kind == "vm":
            return [k for k in names if flat(k.split("@")[0]) == flat(b) or k.split("@")[0].startswith(b + "/")]
        exact = [k for k in names if flat(k) == flat(b)]
        return exact[-1:] or [k for k in names if k.startswith(b + "/")][-1:]

    def _queue_result(self, p, a):
        body = "\n".join(l for l in visible_lines(p.body)
                         if not re.match(r"^\W*(to|from):", TAGS.sub("", l)))
        head = re.split(r"\n\s*\n", body.strip(), maxsplit=1)[0]
        first = re.split(r"(?<=[.!])\s|\n", re.sub(r"^\W*(?:@[\w-]+[\s,:]*)+(?:\([^)]*\)[\s,:]*)?", "", head),
                         maxsplit=1)[0]
        low = first.lower()
        # a result post says so in its first sentence: it starts with the branch, "Enqueued",
        # "Re-enqueued", "Conflict:" or "Running", or it says "landed: `lean` is"
        # "All eight are re-queued at the commits you sent: `a`, `b`, ..." anywhere in the paragraph
        for sent in re.split(r"(?<=[.!:])\s+(?=[A-Z*])", head):
            if re.search(r"\b(are|is|was|were|been|have|has|I)\s+re-?(?:en)?queued\b", sent):
                for x in re.findall(r"`([^`\s]+)`", sent):
                    for b in self._branch(x, "queue"):
                        it = self.items[f"queue:{b}"]
                        if it.state != "closed":
                            it.to, it.state, it.owner = self.reg.queue_handles() or ["all"], "acked", a
                            it.text = f"land-queue: {b} (re-enqueued)"
                            it.history.append((p.created, a, "re-enqueued", p.url))
                            self.queue_posts.add(p.id)
        bare = re.match(r"^\W*([\w./-]+)\W*(?:\([^)]*\)\W*)?(?:landed|did not land)\b", first)
        bare = bare[1] if bare and self._branch(bare[1], "queue") else None
        if not re.match(r"^\W*(`|(re-?)?enqueued\b|conflict\b|running\b|held\b)", low) and not bare \
                and not re.search(r"landed: `lean` is|\bfinished\b", low):
            return
        ticks = re.findall(r"`([^`]+)`", first)
        mentioned = ["@" + m for m in re.findall(r"@([\w-]+)", head)]
        # vm-build: "running `vm-build: B SHA`" / "running `CMD` on `B` `SHA`" (ack), "... finished" (done)
        if re.search(r"\b(running|finished)\b", low) and ("vm-build" in low or re.search(r"\brunning\b", low)):
            names = [x.split()[1] for x in ticks if x.startswith("vm-build:") and len(x.split()) > 1]
            names += [x for x in ticks if not x.startswith("vm-build:")]
            shas = [w for x in ticks for w in x.split() if re.fullmatch(r"[0-9a-f]{7,40}", w)]
            for nm in dict.fromkeys(names):
                for k in self._branch(nm, "vm"):
                    it = self.items[f"vm-build:{k}"]
                    if shas and not any(k.split("@")[1].startswith(s[:10]) or s.startswith(k.split("@")[1])
                                        for s in shas):
                        continue
                    if it.state == "closed":
                        continue
                    self.queue_posts.add(p.id)
                    if re.search(r"\bfinished\b", low):
                        it.state, it.closed_by, it.how = "closed", a, "finished"
                    else:
                        it.state, it.owner = "acked", a
                    it.history.append((p.created, a, "finished" if it.state == "closed" else "running", p.url))
            return
        found = [(m.start(), k) for k, rx in (("failed", r"did not land|\bfailed\b|conflicts? with current|"
                                                         r"^\W*conflict\b|does not merge cleanly|"
                                                         r"came back \W*(conflict|failed)|^\W*held\b|out of the queue"),
                                              ("landed", r"\blanded\b"),
                                              ("enqueued", r"^\W*(?:re-?)?(?:en)?queued\b"))
                 for m in [re.search(rx, low)] if m]
        if not found:
            return
        kind = min(found)[1]
        names = ([bare] if bare else []) + [x for x in ticks if " " not in x and x != "lean"
                                            and not re.fullmatch(r"[0-9a-f]{7,40}", x)]
        if kind == "failed":
            names = names[:1]
        for nm in names:
            bs = self._branch(nm, "queue")
            if not bs and kind == "enqueued" and nm is names[0]:   # enqueued without a line we saw
                it = self._new(Item(f"queue:{nm}", "land-queue", self.reg.queue_handles() or ["all"],
                                    mentioned[0] if mentioned else a, p.created, p.url, p.where(),
                                    f"land-queue: {nm}"))
                bs = [nm]
            for b in bs:
                self.queue_posts.add(p.id)
                it = self.items[f"queue:{b}"]
                if it.state == "closed":
                    if kind != "enqueued":
                        continue
                    it = self._new(Item(it.id, "land-queue", it.to, it.asker, p.created, p.url,
                                        p.where(), it.text))
                if kind == "enqueued":   # = ack: the queue has it
                    if it.state == "open" and it.to == [it.asker]:
                        it.text = f"land-queue: {b} (re-enqueued)"
                    it.to, it.state, it.owner = self.reg.queue_handles() or ["all"], "acked", a
                elif kind == "landed":
                    it.state, it.closed_by, it.how = "closed", a, "landed"
                else:   # back to the asker, who fixes and re-sends it, or closes it
                    it.to, it.state, it.owner = [it.asker], "open", None
                    it.text = (first if "did not land" in low else "did not land: " + first)[:160]
                it.history.append((p.created, a, kind, p.url))
                it.url = p.url

    # ----- views

    def handles_of(self, h):
        """What an item's `to` may name for handle h: h, its @account (unsigned posts), and, for a
        `relay` session, its owner."""
        h = self.reg.canon(h)
        s = self.reg.get(h)
        out = {h}
        if s and not s.human:
            out.add("@" + s.account)
            if "relay" in s.claims:
                out.add(s.owner)
        return out

    def for_handle(self, it, h):
        names = self.handles_of(h)
        return bool(names & set(it.to)) or ("all" in it.to and it.asker not in names)

    def by_handle(self, it, h):
        s = self.reg.get(h)
        return it.asker == self.reg.canon(h) or bool(s and it.asker == "@" + s.account and
                                                    it.kind in ("land", "review"))

    def open_items(self, for_=None, by=None, closed=False):
        out = [i for i in self.items.values() if closed or i.state != "closed"]
        if for_:
            out = [i for i in out if self.for_handle(i, for_)]
        if by:
            out = [i for i in out if self.by_handle(i, by)]
        return sorted(out, key=lambda i: i.created)


# ---------------------------------------------------------------- the GitHub API (ETags, since=, backoff)

class GitHubError(Exception):
    pass


class GitHub:
    """GET only. Each URL's ETag is kept with its response, so an unchanged page costs a 304."""

    def __init__(self, token, cache_dir, opener=urllib.request.urlopen, sleep=time.sleep, log=None):
        if not token:
            raise GitHubError("GH_TOKEN is not set")
        self._token, self.opener, self.sleep = token, opener, sleep
        self.log = log or (lambda s: print(s, file=sys.stderr, flush=True))
        self.dir = os.path.join(cache_dir, "http")
        os.makedirs(self.dir, exist_ok=True)
        self.etags_path = os.path.join(cache_dir, "etags.json")
        self.etags = load_json(self.etags_path, {})
        self.calls = self.not_modified = 0

    def _file(self, url):
        return os.path.join(self.dir, hashlib.sha1(url.encode()).hexdigest() + ".json")

    def get(self, url):
        """One page: (json, the next page's URL or None)."""
        backoff = 5
        for attempt in range(8):
            hdr = {"Authorization": "Bearer " + self._token, "Accept": "application/vnd.github+json",
                   "X-GitHub-Api-Version": "2022-11-28", "User-Agent": "gh-inbox"}
            f = self._file(url)
            if url in self.etags and os.path.exists(f):
                hdr["If-None-Match"] = self.etags[url]
            self.calls += 1
            try:
                with self.opener(urllib.request.Request(url, headers=hdr), timeout=60) as r:
                    data, headers = r.read(), r.headers
            except urllib.error.HTTPError as e:
                e.close()
                if e.code == 304:
                    self.not_modified += 1
                    cached = load_json(f, None)
                    if cached is not None:
                        return cached["data"], cached.get("next")
                    self.etags.pop(url, None)
                    continue
                wait = self._limit_wait(e.code, e.headers)
                if wait is not None:
                    self.log(f"gh-inbox: rate limited (HTTP {e.code}), waiting {wait}s")
                    self.sleep(wait)
                    continue
                if e.code >= 500 and attempt < 7:
                    self.sleep(backoff)
                    backoff = min(backoff * 2, 300)
                    continue
                raise GitHubError(f"GET {url.split('?')[0]}: HTTP {e.code}") from None
            except (urllib.error.URLError, TimeoutError, ConnectionError, OSError):
                if attempt == 7:
                    raise GitHubError(f"GET {url.split('?')[0]}: network error") from None
                self.sleep(backoff)
                backoff = min(backoff * 2, 300)
                continue
            body = json.loads(data or b"null")
            m = re.search(r'<([^>]+)>;\s*rel="next"', headers.get("Link") or "")
            nxt = m[1] if m else None
            if headers.get("ETag"):
                save_json(f, {"data": body, "next": nxt})
                self.etags[url] = headers["ETag"]
                save_json(self.etags_path, self.etags)
            rem = headers.get("X-RateLimit-Remaining")
            if rem is not None and rem.isdigit() and int(rem) < 100:
                self.log(f"gh-inbox: {rem} API calls left before the limit resets")
            return body, nxt
        raise GitHubError(f"GET {url.split('?')[0]}: gave up")

    @staticmethod
    def _limit_wait(code, headers):
        if code not in (403, 429):
            return None
        ra = headers.get("Retry-After")
        if ra and ra.isdigit():
            return min(int(ra), 3600)
        if headers.get("X-RateLimit-Remaining") == "0":
            reset = int(headers.get("X-RateLimit-Reset") or 0)
            return max(1, min(3600, reset - int(time.time()) + 1))
        return 60 if code == 429 else None

    def pages(self, path, **params):
        url = f"{API}/{path}?{urllib.parse.urlencode(params)}"
        out = []
        while url:
            data, url = self.get(url)
            out += data if isinstance(data, list) else [data]
        return out


def load_json(path, default):
    try:
        with open(path) as f:
            return json.load(f)
    except (OSError, ValueError):
        return default


def save_json(path, obj):
    tmp = path + ".tmp"
    with open(tmp, "w") as f:
        json.dump(obj, f)
    os.replace(tmp, path)


# ---------------------------------------------------------------- the cache of the threads

def norm_comment(c, repo):
    return {"id": str(c["id"]), "repo": repo, "number": int(c["issue_url"].rsplit("/", 1)[1]),
            "kind": "comment", "login": c["user"]["login"], "url": c["html_url"],
            "created": c["created_at"], "updated": c["updated_at"], "body": c.get("body") or ""}


def norm_issue(i, repo):
    return {"id": f"{repo}#{i['number']}", "repo": repo, "number": i["number"],
            "kind": "pr" if "pull_request" in i else "issue", "login": i["user"]["login"],
            "url": i["html_url"], "title": i["title"], "created": i["created_at"],
            "updated": i["updated_at"], "body": i.get("body") or ""}


def norm_pull(p, repo):
    return {"repo": repo, "number": p["number"], "login": p["user"]["login"], "title": p["title"],
            "url": p["html_url"], "draft": bool(p.get("draft")), "created": p["created_at"],
            "updated": p["updated_at"], "reviewers": [r["login"] for r in p.get("requested_reviewers", [])],
            "head": (p.get("head") or {}).get("ref"), "sha": (p.get("head") or {}).get("sha")}


class Store:
    """The threads as last fetched, and the cursor (the newest `updated_at` seen per repository
    and endpoint), so a restart resumes where the last run stopped."""

    def __init__(self, cache_dir):
        self.dir = cache_dir
        os.makedirs(cache_dir, exist_ok=True)
        self.path = os.path.join(cache_dir, "threads.json")
        d = load_json(self.path, {})
        self.posts, self.marks = d.get("posts", {}), d.get("marks", {})
        self.pulls = d.get("pulls", {})
        self.reviews = {k: v for k, v in d.get("reviews", {}).items() if isinstance(v, dict)}

    def save(self):
        save_json(self.path, {"posts": self.posts, "marks": self.marks, "pulls": self.pulls,
                              "reviews": self.reviews})

    def all_pulls(self):
        return [p for r in REPOS for p in self.pulls.get(r, [])]

    def sync(self, gh, since, my_accounts=()):
        for r in REPOS:
            m = self.marks.setdefault(r, {})
            for ep, norm in (("issues/comments", norm_comment), ("issues", norm_issue)):
                w = m.get(ep, since)
                extra = {"state": "all"} if ep == "issues" else {}
                for c in gh.pages(f"repos/{OWNER}/{r}/{ep}", since=w, sort="updated", direction="asc",
                                  per_page=100, **extra):
                    p = norm(c, r)
                    self.posts[p["id"]] = p
                    m[ep] = max(m.get(ep, w), p["updated"])
            self.pulls[r] = [norm_pull(p, r) for p in
                             gh.pages(f"repos/{OWNER}/{r}/pulls", state="open", per_page=100)]
            for pr in self.pulls[r]:   # reviews of my own open PRs, when the PR changed
                k = f"{r}#{pr['number']}"
                if pr["login"] in my_accounts and self.reviews.get(k, {}).get("updated") != pr["updated"]:
                    revs = gh.pages(f"repos/{OWNER}/{r}/pulls/{pr['number']}/reviews", per_page=100)
                    self.reviews[k] = {"updated": pr["updated"], "reviews": [
                        {"id": v["id"], "login": v["user"]["login"], "state": v["state"],
                         "url": v.get("html_url") or pr["url"]} for v in revs if v.get("user")]}
        self.save()

    def model(self, reg):
        return Model(reg, list(self.posts.values()), self.all_pulls())


# ---------------------------------------------------------------- watch

class Watcher:
    """Turns successive models into one line per new event for one session."""

    def __init__(self, reg, me, state_path, sigs=(), threads=(), remind=6 * 3600, backlog=0):
        self.reg, self.me = reg, reg.canon(me)
        s = reg.get(me)
        self.accounts = {s.account} if s else set()
        self.owner = s.owner if s else None
        self.relay = bool(s and "relay" in s.claims)
        self.sigs = list(sigs) + (s.sigs if s else [])
        self.aliases = [self.me] + (s.aliases if s else [])
        self.threads, self.remind, self.backlog = set(threads), remind, backlog
        self.path = state_path
        st = load_json(state_path, {}) if state_path else {}
        self.seen = set(st.get("seen", []))
        self.items = st.get("items", {})
        self.reminded = st.get("reminded", {})
        self.reviews = set(st.get("reviews", []))
        self.started = st.get("started", False)

    def save(self):
        if self.path:
            save_json(self.path, {"seen": sorted(self.seen), "items": self.items, "started": True,
                                  "reminded": self.reminded, "reviews": sorted(self.reviews)})

    def mine(self, p):
        """Mine only by my exact `from:` line, or, on a post without one, my legacy signature at
        its end. Never by a mention: others address me by my handle."""
        if p.frm:
            return self.reg.canon(p.frm).lower() == self.me.lower()
        tail = "\n".join([l for l in visible_lines(p.body) if l.strip()][-3:])
        return any(sig in tail for sig in self.sigs)

    def why(self, p):
        """Why a post that is not mine concerns me, or None."""
        if p.to is not None:
            to = {self.reg.canon(t).lower() for t in p.to}
            if self.me.lower() in to:
                return "to-me"
            if self.relay and self.owner and self.owner.lower() in to:
                return f"to-{self.owner}"
            if "all" in to:
                return "to-all"
        else:   # a legacy post: my handle or an alias as a word, or an @-mention of my account
            for al in self.aliases:
                if re.search(word_re(al), p.body, re.I):
                    return "legacy-mention"
            for acc in self.accounts:
                if re.search(rf"@{re.escape(acc)}(?![\w-])", p.body):
                    return "legacy-@" + acc
            if self.relay and self.owner and re.search(rf"@{re.escape(self.owner)}(?![\w-])", p.body):
                return f"legacy-@{self.owner}"
        return "thread" if p.where() in self.threads else None

    def concerns(self, it, model):
        return model.for_handle(it, self.me) or model.by_handle(it, self.me)

    def step(self, model, now, reviews=None):
        out = []
        first = not self.started
        emit = lambda when, tag, text: out.append(re.sub(r"\s+", " ", f"{when[11:16]}Z [{tag}] {text}")[:500])
        shown = set()   # the posts an item's line below stands for
        cur = {}
        for it in model.items.values():
            if not self.concerns(it, model):
                continue
            snap = cur[it.id] = [it.state, it.owner, it.updated, ",".join(it.to)]
            prev = self.items.get(it.id)
            to_me = model.for_handle(it, self.me)
            if prev is None:
                if it.state != "closed" and to_me and not first:
                    emit(it.history[-1][0], it.kind, it.line(now))
                    shown.add(it.history[-1][3])
                elif it.state != "closed" and first:
                    emit(iso(now), "open" if to_me else "waiting", it.line(now))
            elif prev[0] != snap[0] or prev[1] != snap[1] or prev[3] != snap[3]:
                when, who, what, url = [h for h in it.history
                                        if "ignored" not in h[2] and "already closed" not in h[2]][-1]
                if who == self.me:   # my own ack or answer
                    continue
                shown.add(url)
                tag = it.kind if (to_me and it.state == "open") else it.state
                emit(when, tag, f"{it.id} {what} by {who}; now {it.state} to {','.join(it.to)}"
                     f"{' owner ' + it.owner if it.owner and it.state == 'acked' else ''}: {it.text[:160]} <{url}>")
            elif it.kind == "land" and prev[2] and snap[2] != prev[2] and it.state != "closed":
                emit(snap[2], "pr-updated", it.line(now))
        for iid, prev in self.items.items():   # gone from GitHub: the PR merged or closed, review done
            if iid not in cur and prev[0] != "closed" and iid.split(":")[0] in ("land", "review"):
                emit(iso(now), "closed", f"{iid} no longer open on GitHub")
        horizon = iso(now - datetime.timedelta(seconds=self.backlog))
        for p in model.posts:
            if p.id in self.seen:
                continue
            self.seen.add(p.id)
            if (first and p.created < horizon) or self.mine(p) or p.url in shown:
                continue   # a post an item's line above stands for is not printed twice
            w = self.why(p)
            if w:
                emit(p.created, w, f"{p.where()} {p.id} {model.author[p.id]}: {p.summary()} <{p.url}>")
        self.items = cur
        for it in model.open_items(for_=self.me):
            if it.state != "open":
                continue
            last = self.reminded.setdefault(it.id, iso(now))
            if not first and (now - ts(last)).total_seconds() >= self.remind:
                emit(iso(now), "still-open", it.line(now))
                self.reminded[it.id] = iso(now)
        for k, rv in (reviews or {}).items():
            for v in rv.get("reviews", []):
                if str(v["id"]) not in self.reviews:
                    self.reviews.add(str(v["id"]))
                    if not first and v["login"] not in self.accounts:
                        emit(iso(now), "review", f"{k} {v['state']} by {v['login']} <{v['url']}>")
        self.started = True
        return out


# ---------------------------------------------------------------- scan (back-filling legacy asks)

ASKY = re.compile(r"\?\s*\**$|\b(please|could you|can you|ok to|approve\??|let me know|please say)\b", re.I)


def scan(model, since, now):
    """Legacy posts since `since` that look like asks to a registered session or person, with no
    later post in the thread by one of them and no `re:` naming them. Proposes only."""
    reg, out = model.reg, []
    answered = {t for p in model.posts for _, ts_, _, _ in p.actions() for t in ts_}
    for p in model.posts:
        if p.created < since or p.convention or p.id in model.queue_posts or p.id in answered:
            continue
        q = [s.strip() for l in visible_lines(p.body) for s in re.split(r"(?<=[.?!])\s+", l)
             if ASKY.search(s.strip())]
        if not q:
            continue
        a = model.author[p.id]
        to = [s.handle for s in reg.sessions.values() if s.handle != a and not s.human and
              any(re.search(word_re(x), p.body, re.I) for x in [s.handle] + s.aliases)]
        accs = {reg.get(h).account for h in to}
        to += [h for h in (reg.human_by_login(x) for x in re.findall(r"@([\w-]+)", p.body))
               if h and h != a and reg.get(h).account not in accs]   # @kaashoek (dsverify-lab session)
        accs = {reg.get(h).account for h in to}
        to += ["@" + x for x in re.findall(r"@([\w-]+)", p.body)
               if x not in accs and not reg.human_by_login(x) and x != p.login]
        to = list(dict.fromkeys(to))
        if not to:
            continue
        accounts = {reg.get(t).account for t in to if reg.get(t)} | {t[1:] for t in to if t.startswith("@")}
        later = [o for o in model.posts if o.where() == p.where() and o.created > p.created
                 and (model.author[o.id] in to or (o.login in accounts and model.author[o.id] != a))]
        if later:
            continue
        text = q[-1][:200]
        out.append(f"{p.id} {p.where()} age {age(p.created, now)} from {a} to {','.join(to)}: {text} <{p.url}>\n"
                   f"    to confirm: post on {p.where()} `to: {', '.join(t.lstrip('@') for t in to)}` and "
                   f"`ask: {text} (back-filled from {p.url})`; to drop: nothing")
    return out


# ---------------------------------------------------------------- commands

def cache_dir(args, handle):
    """`watch --me H` keeps its cache in <root>/H; the listing commands share <root>/_any unless
    given --me."""
    return os.path.join(args.cache or os.path.expanduser("~/.cache/gh-inbox"), handle or "_any")


def load_model(args, reg, handle):
    st = Store(cache_dir(args, handle))
    if not args.offline:
        since = iso(now_utc() - datetime.timedelta(days=args.days))
        st.sync(GitHub(os.environ.get("GH_TOKEN"), st.dir), since)
    return st.model(reg)


def cmd_watch(args, reg):
    me = reg.canon(args.me)
    s = reg.get(me)
    if not s:
        print(f"gh-inbox: warning: {me} is not in {args.registry}", file=sys.stderr)
    d = cache_dir(args, me)
    w = Watcher(reg, me, os.path.join(d, "watch.json"), sigs=args.sig, threads=args.thread,
                remind=args.remind, backlog=args.backlog)
    st = Store(d)
    gh = None if args.offline else GitHub(os.environ.get("GH_TOKEN"), d)
    since = iso(now_utc() - datetime.timedelta(days=args.days))
    while True:
        lines = []
        try:
            if gh:
                st.sync(gh, since, {s.account} if s else set())
            lines = w.step(st.model(reg), now_utc(), st.reviews)
            for line in lines:
                print(line, flush=True)
            w.save()
        except GitHubError as e:
            print(f"gh-inbox: {e}", file=sys.stderr, flush=True)
        if args.once or (args.until_event and lines):
            return 0
        time.sleep(args.interval)


def cmd_open(args, reg):
    h = reg.canon(args.for_) if args.for_ else None
    by = reg.canon(args.by) if args.by else None
    m = load_model(args, reg, args.me)
    now = now_utc()
    items = m.open_items(h, by, closed=args.closed)
    for it in items:
        print(it.line(now))
    if not items:
        print("no open items" + (f" for {h}" if h else "") + (f" by {by}" if by else ""))
    return 0


def cmd_digest(args, reg):
    h = reg.canon(args.for_)
    print(digest(load_model(args, reg, args.me), h, now_utc()))
    return 0


def digest(m, h, now):
    items = [i for i in m.open_items() if h in i.to]
    if not items:
        return f"Nothing is waiting on {h}."
    groups = [("Decisions", "decision"), ("Asks", "ask"), ("Reviews requested", "review"),
              ("Pull requests to land", "land"), ("Land requests", "land-queue"), ("VM builds", "vm-build")]
    out = [f"Waiting on {h}: {len(items)}, oldest first."]
    for title, kind in groups:
        g = [i for i in items if i.kind == kind]
        if g:
            out.append(f"\n{title}:")
            out += [f"- {age(i.created, now)} {i.where} from {i.asker}"
                    f"{' (' + i.owner + ' on it)' if i.state == 'acked' else ''}: {i.text} "
                    f"(`{i.id}`) <{i.url}>" for i in g]
    return "\n".join(out)


def build_post(reg, me, to, body, ask=None, mention=True):
    """The body with its `to:` first line and `from:` last line added."""
    bad = [t for t in to if not reg.known(t)]
    if bad:
        raise SystemExit(f"gh-inbox: unknown handle(s) {', '.join(bad)} (etc/sessions.txt)")
    if not reg.get(me):
        raise SystemExit(f"gh-inbox: --me {me} is not in etc/sessions.txt")
    me, to = reg.canon(me), [reg.canon(t) for t in to]
    lines = body.strip("\n").splitlines()
    ne = [l for l in lines if l.strip()]
    if ne and (re.match(r"^\s*to:", ne[0]) or re.match(r"^\W*from:", TAGS.sub("", ne[-1]))):
        raise SystemExit("gh-inbox: FILE has its own to:/from: line; the tool adds them")
    probe = Post({"id": "0", "repo": "", "number": 0, "kind": "comment", "login": "", "url": "",
                  "created": "", "updated": "", "body": body})
    if ask is True and not any(k == "ask" for k, _ in probe.lines):
        raise SystemExit("gh-inbox: --ask without TEXT needs an `ask:` line in FILE")
    mine = reg.get(me).account
    accs = list(dict.fromkeys(reg.get(t).account for t in to if reg.get(t) and reg.get(t).account
                              not in ("", "-", mine)))
    head = "to: " + ", ".join(to) + (" (" + " ".join("@" + a for a in accs) + ")" if mention and accs else "")
    tail = [f"ask: {ask}"] if isinstance(ask, str) else []
    return "\n".join([head, ""] + lines + ([""] + tail if tail else []) + ["", f"from: {me}"]) + "\n"


def cmd_post(args, reg):
    with open(args.file) as f:
        body = build_post(reg, args.me, args.to, f.read(), args.ask, not args.no_mention)
    out = args.output or args.file + ".post"
    with open(out, "w") as f:
        f.write(body)
    repo = short_repo(args.repo)
    print(body, end="")
    print(f"--- written to {out}; the tool never posts. To post it:\n"
          f"gh api repos/{OWNER}/{repo}/issues/{args.issue}/comments -F body=@{shlex.quote(os.path.abspath(out))}")
    return 0


def cmd_scan(args, reg):
    m = load_model(args, reg, args.me)
    since = args.since if "T" in args.since else args.since + "T00:00:00Z"
    out = scan(m, since, now_utc())
    print("\n".join(out) if out else "no legacy post looks like an open ask")
    print("(dry run: the tool never posts; a proposal becomes an item only when someone posts its ask)",
          file=sys.stderr)
    return 0


def cmd_show(args, reg):
    m = load_model(args, reg, args.me)
    its = m._resolve(norm_id(args.id) or args.id)
    if not its:
        print(f"no item {args.id}")
        return 1
    now = now_utc()
    for it in its:
        print(it.line(now))
        for when, who, what, url in it.history:
            print(f"  {when} {who}: {what} <{url}>")
    return 0


def main(argv=None):
    argv = list(sys.argv[1:] if argv is None else argv)
    argv = ["open" if a == "--open" else a for a in argv]   # `--open` as the proposal spelled it
    ap = argparse.ArgumentParser(prog="gh-inbox.py", description=__doc__.split("\n\n")[0])
    ap.add_argument("--registry", default=REGISTRY)
    ap.add_argument("--cache", help="cache root (default ~/.cache/gh-inbox)")
    ap.add_argument("--offline", action="store_true", help="use the cache only, no API calls")
    ap.add_argument("--days", type=int, default=21, help="history fetched by a first sync (default 21)")
    sub = ap.add_subparsers(dest="cmd", required=True)
    w = sub.add_parser("watch", help="print one line per event for a session")
    w.add_argument("--me", required=True)
    w.add_argument("--interval", type=duration, default=120)
    w.add_argument("--backlog", type=duration, default=0, help="on a first run, also print posts this recent")
    w.add_argument("--remind", type=duration, default=6 * 3600, help="reprint an ask to me open this long")
    w.add_argument("--sig", action="append", default=[], help="another legacy signature of mine")
    w.add_argument("--thread", action="append", default=[], help="REPO#N: print every post there")
    w.add_argument("--once", action="store_true", help="one poll, then exit")
    w.add_argument("--until-event", action="store_true", help="poll until something is printed, then exit")
    o = sub.add_parser("open", help="open and acked items")
    o.add_argument("--for", dest="for_", help="addressed to this handle")
    o.add_argument("--by", help="asked by this handle (what it waits on)")
    o.add_argument("--me", help="whose cache to use")
    o.add_argument("--closed", action="store_true", help="closed items too")
    g = sub.add_parser("digest", help="what is waiting on a person")
    g.add_argument("--for", dest="for_", default="upamanyus")
    g.add_argument("--me")
    p = sub.add_parser("post", help="add the to:/from: lines to FILE (never posts)")
    p.add_argument("--me", default=os.environ.get("GH_INBOX_ME"), required=not os.environ.get("GH_INBOX_ME"))
    p.add_argument("--to", nargs="+", required=True)
    p.add_argument("--issue", type=int, required=True)
    p.add_argument("--repo", default="etcd-grove")
    p.add_argument("--ask", nargs="?", const=True, default=None,
                   help="add `ask: TEXT`; without TEXT, require an ask: line in FILE")
    p.add_argument("--no-mention", action="store_true", help="no @accounts on the to: line")
    p.add_argument("-o", "--output", help="where to write the body (default FILE.post)")
    p.add_argument("file")
    s = sub.add_parser("scan", help="legacy posts that look like open asks (proposals only)")
    s.add_argument("--since", required=True)
    s.add_argument("--dry-run", action="store_true", help="the default and only mode")
    s.add_argument("--me")
    sh = sub.add_parser("show", help="one item's history")
    sh.add_argument("id")
    sh.add_argument("--me")
    args = ap.parse_args(argv)
    reg = Registry.load(args.registry)
    try:
        return {"watch": cmd_watch, "open": cmd_open, "digest": cmd_digest, "post": cmd_post,
                "scan": cmd_scan, "show": cmd_show}[args.cmd](args, reg)
    except GitHubError as e:
        print(f"gh-inbox: {e}", file=sys.stderr)
        return 1
    except KeyboardInterrupt:
        return 130


if __name__ == "__main__":
    sys.exit(main())
