#!/usr/bin/env python3
"""Check Lean files incrementally, through a Lean server kept running between checks.

    etc/lean-check.py FILE...                  check FILEs (as they are on disk)
    etc/lean-check.py FILE --goal LINE[:COL]   ... and print the goal there
    etc/lean-check.py --status | --stop        the server's open files | stop it

`lake build` and `lake env lean` elaborate a file from the start every time. Lean's
server instead keeps a snapshot after every command and every tactic of a proof (of a
tactic sequence, a `·` block, `case`, `next`, the alternatives of `cases`/`induction`):
after an edit it re-elaborates only from the first changed tactic on. This script
keeps one server (`lake serve`) running in the background, with the files it checked
open, and sends it a file's new contents on each check, so that a check after an edit
near the end of a 5-minute proof takes seconds. The first check of a file elaborates
it in full, like `lake build`.

A check prints the file's errors and warnings (`-q`: only errors) as `lake build`
does, `FILE:LINE:COL: error: ...`, with the time it took and whether it reused the
open file (`incremental`) or opened it (`fresh`), and exits 1 if there are errors.
Lines are 1-based, columns 0-based, as in Lean's messages. `--goal LINE[:COL]` (COL
defaults to the line's end) prints the proof state there, the goals before the tactic
at that position, after the check; `--goal` may be repeated. `-e`/`--first-error` returns
as soon as the server reports an error in what the edit changed (from the first changed line to
the end of its declaration; anywhere on a first check), or as soon as that declaration is
elaborated without one, printing the messages so far, older errors elsewhere in the file
included; the server goes on elaborating the rest (the declarations after it, and, when the
early return is for an error, the once-per-declaration work), which the next check reuses or
cancels.

What an edit costs: the tactics from the edit on, then, for the declaration edited, the
work done once its proof is complete, which no snapshot saves: instantiating its proof
term, the kernel's check of it (about half: 6.4 of 13.8s after an edit at the end of
`lessor__sendKeepAliveLoop`), the linters. `--fast` skips the kernel's check
(`debug.skipKernelTC`) and the linters that walk the whole proof (unused variables, unused
simp arguments, unreachable tactics): for the edit loop only, since a proof the elaborator
accepts can still fail the kernel; `lake build` checks everything. The options go on the
blank line after the file's imports in the server's copy (so that no line moves; without
such a line `--fast` does nothing). Switching a file to or from `--fast` reopens it.

`--split` makes the server prove each `·` block of at least N lines (`--split-min N`, 20) as
an auxiliary theorem (`Proof/AbstractBullets.lean`, option `abstractBullets`, whose import it
appends to the file's last import line in the server's copy): a block's proof is then
instantiated and checked when the block ends, part of the snapshot after it, and what is left
to do once the declaration is complete is only the proof outside the long blocks. It pays for
the longest proofs; see `CLAUDE.md`, "Checking a proof while editing it".

Imports: when a check finds that a file an open file imports (transitively, in this
repository or its packages) changed since the file was opened, it reopens the file:
the server rebuilds the changed imports with Lake (as `lake build` would) and
elaborates the file in full. Edits to the file's own `import` lines do the same.

The background server is started on the first check (`.lake/lean-check/`: its socket
and log), keeps at most `--max-open` files open (default 4; each open file is a Lean
process holding its imports, 2-5 GiB), closing the least recently checked one, and
exits after `--idle` minutes without a check (default 60). Standard library only.
"""

import argparse
import hashlib
import json
import os
import socket
import subprocess
import sys
import threading
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
STATE = os.path.join(ROOT, ".lake", "lean-check")
SOCK = os.path.join(STATE, "sock")
LOG = os.path.join(STATE, "log")


# --- imports -------------------------------------------------------------------------

def source_roots():
    """The directories module names resolve in: this repository and each package's."""
    roots = [ROOT]
    pkgs = os.path.join(ROOT, ".lake", "packages")
    try:
        manifest = json.load(open(os.path.join(ROOT, "lake-manifest.json")))
        for p in manifest.get("packages", []):
            d = os.path.join(pkgs, p["name"])
            roots.append(os.path.join(d, p["subDir"]) if p.get("subDir") else d)
    except (OSError, ValueError, KeyError):
        pass
    return roots


_import_cache = {}  # file -> (mtime, [module names])


def file_imports(path):
    """The modules `path` imports, from its header (cached by modification time)."""
    try:
        mt = os.stat(path).st_mtime_ns
    except OSError:
        return []
    hit = _import_cache.get(path)
    if hit and hit[0] == mt:
        return hit[1]
    mods = []
    with open(path, encoding="utf-8", errors="replace") as f:
        in_comment = 0
        for line in f:
            s = line.strip()
            if in_comment:
                if "-/" in s:
                    in_comment = 0
                continue
            if s.startswith("/-"):
                if "-/" not in s[2:]:
                    in_comment = 1
                continue
            if not s or s.startswith("--") or s == "module" or s.startswith("prelude"):
                continue
            words = s.split()
            while words and words[0] in ("public", "private", "meta", "import", "all"):
                if words[0] == "import":
                    mods.extend(w for w in words[1:] if w not in ("all",) and not w.startswith("--"))
                    break
                words = words[1:]
            else:
                break
            if not words or words[0] != "import":
                break
    _import_cache[path] = (mt, mods)
    return mods


def module_file(mod, roots):
    rel = mod.replace(".", os.sep) + ".lean"
    for r in roots:
        p = os.path.join(r, rel)
        if os.path.exists(p):
            return p
    return None  # Lean's own modules: they do not change


_hash_cache = {}  # file -> (mtime, content hash)


def content_hash(path):
    """`path`'s content hash (cached by modification time: a file edited and restored, or
    touched, is unchanged)."""
    mt = os.stat(path).st_mtime_ns
    hit = _hash_cache.get(path)
    if hit and hit[0] == mt:
        return hit[1]
    h = hashlib.sha1(open(path, "rb").read()).hexdigest()
    _hash_cache[path] = (mt, h)
    return h


def import_closure(path, roots):
    """The source files `path` imports, transitively, with their content hashes."""
    seen = {}
    stack = [path]
    while stack:
        f = stack.pop()
        for m in file_imports(f):
            mf = module_file(m, roots)
            if mf and mf not in seen:
                try:
                    seen[mf] = content_hash(mf)
                except OSError:
                    continue
                stack.append(mf)
    return seen


# --- the Lean server -------------------------------------------------------------------

class Server:
    """One `lake serve`, with a set of open files."""

    def __init__(self, max_open):
        self.max_open = max_open
        self.lock = threading.Lock()       # writing to the server
        self.state = threading.Condition()  # responses, diagnostics, progress
        self.next_id = 0
        self.responses = {}
        self.diags = {}      # uri -> (version, [diagnostic])
        self.progress = {}   # uri -> (version, processing list)
        self.progress_logged = {}  # uri -> when its progress was last logged
        self.busy_versions = {}    # uri -> the versions it has reported in progress
        self.files = {}      # path -> {"version", "text", "deps", "used", "lock"}
        self.files_lock = threading.Lock()
        self.roots = source_roots()
        self.start()

    def start(self):
        self.proc = subprocess.Popen(["lake", "serve"], cwd=ROOT, stdin=subprocess.PIPE,
                                     stdout=subprocess.PIPE, stderr=open(LOG, "ab"))
        self.dead = False
        threading.Thread(target=self.reader, daemon=True).start()
        self.request("initialize", {"processId": os.getpid(), "rootUri": uri_of(ROOT),
                                    "capabilities": {}})
        self.notify("initialized", {})

    def send(self, msg):
        b = json.dumps(msg).encode()
        with self.lock:
            self.proc.stdin.write(b"Content-Length: %d\r\n\r\n" % len(b) + b)
            self.proc.stdin.flush()

    def notify(self, method, params):
        self.send({"jsonrpc": "2.0", "method": method, "params": params})

    def request(self, method, params, timeout=None):
        with self.state:
            self.next_id += 1
            rid = self.next_id
        self.send({"jsonrpc": "2.0", "id": rid, "method": method, "params": params})
        with self.state:
            if not self.state.wait_for(lambda: rid in self.responses or self.dead, timeout):
                raise TimeoutError(method)
            if self.dead:
                raise RuntimeError("the Lean server exited (see %s)" % LOG)
            return self.responses.pop(rid)

    def reader(self):
        f = self.proc.stdout
        try:
            while True:
                n = None
                while True:
                    line = f.readline()
                    if not line:
                        raise EOFError
                    line = line.strip()
                    if not line:
                        break
                    k, _, v = line.decode().partition(":")
                    if k.lower() == "content-length":
                        n = int(v)
                msg = json.loads(f.read(n))
                self.handle(msg)
        except (EOFError, ValueError, OSError):
            with self.state:
                self.dead = True
                self.state.notify_all()

    def handle(self, msg):
        method = msg.get("method")
        if method is None:
            with self.state:
                self.responses[msg.get("id")] = msg
                self.state.notify_all()
        elif "id" in msg:
            # a request from the server (`client/registerCapability`, ...): accept it
            self.send({"jsonrpc": "2.0", "id": msg["id"], "result": None})
        elif method == "textDocument/publishDiagnostics":
            p = msg["params"]
            with self.state:
                self.diags[p["uri"]] = (p.get("version"), p["diagnostics"])
                self.state.notify_all()
        elif method == "$/lean/fileProgress":
            p = msg["params"]
            uri = p["textDocument"]["uri"]
            with self.state:
                self.progress[uri] = (p["textDocument"].get("version"), p["processing"])
                if p["processing"]:
                    self.busy_versions.setdefault(uri, set()).add(p["textDocument"].get("version"))
                self.state.notify_all()
            now = time.time()
            if p["processing"] and now - self.progress_logged.get(uri, 0) > 5:
                self.progress_logged[uri] = now
                with open(LOG, "a") as log:
                    log.write("%s %s v%s at line %d\n" % (
                        time.strftime("%H:%M:%S"), os.path.relpath(uri[7:], ROOT),
                        p["textDocument"].get("version"), first_line(p["processing"])))

    # files

    def check(self, path, goals, fast=False, first_error=False, split=0):
        """Bring the server's copy of `path` up to date and wait for its elaboration."""
        with self.files_lock:
            ent = self.files.get(path)
            if ent is None:
                ent = self.files[path] = {"version": 0, "text": None, "deps": None,
                                          "lock": threading.Lock()}
            ent["used"] = time.time()
        with ent["lock"]:
            return self.check_locked(path, ent, goals, fast, first_error, split)

    def check_locked(self, path, ent, goals, fast, first_error, split):
        t0 = time.time()
        text = open(path, encoding="utf-8").read()
        sent = server_text(text, fast, split)
        if sent is None:  # no blank line after the imports to put the options on
            sent, fast, split = text, False, 0
        uri = uri_of(path)
        mode = "incremental"
        if ent["text"] is not None and ent.get("opts") != (fast, split):
            self.notify("textDocument/didClose", {"textDocument": {"uri": uri}})
            ent["text"] = None
            mode = "reopened (other options)"
        if ent["text"] is not None:
            deps = import_closure(path, self.roots)
            stale = [d for d, h in deps.items() if ent["deps"].get(d) != h]
            if stale or file_imports_text(text) != file_imports_text(ent["text"]):
                self.notify("textDocument/didClose", {"textDocument": {"uri": uri}})
                ent["text"] = None
                mode = "reopened (%s changed)" % (
                    os.path.relpath(stale[0], ROOT) + (" and %d more" % (len(stale) - 1)
                                                      if len(stale) > 1 else "")
                    if stale else "imports")
        # the lines whose errors `-e` returns at (0-based, end exclusive): the declaration the
        # edit starts in, from the first changed line on (everything on a fresh open)
        watch = (0, None)
        if ent["text"] is not None and text != ent["text"]:
            watch = edited_region(ent["text"], text)
        if ent["text"] is None:
            if mode == "incremental":
                mode = "fresh"
            self.evict(path)
            ent["deps"] = import_closure(path, self.roots)
            ent["version"] += 1
            self.notify("textDocument/didOpen", {"textDocument": {
                "uri": uri, "languageId": "lean4", "version": ent["version"], "text": sent}})
        elif text != ent["text"]:
            ent["version"] += 1
            self.notify("textDocument/didChange", {
                "textDocument": {"uri": uri, "version": ent["version"]},
                "contentChanges": [{"text": sent}]})
        else:
            mode = "unchanged"
        ent["text"] = text
        ent["opts"] = (fast, split)
        v = ent["version"]
        done = threading.Event()

        def wait_all():
            try:
                self.request("textDocument/waitForDiagnostics", {"uri": uri, "version": v})
            finally:
                done.set()
                with self.state:
                    self.state.notify_all()

        threading.Thread(target=wait_all, daemon=True).start()

        def has_error():
            ver, ds = self.diags.get(uri, (None, []))
            return ver == v and any(
                d.get("severity", 1) == 1 and watch[0] <= d["range"]["start"]["line"]
                and (watch[1] is None or d["range"]["start"]["line"] < watch[1]) for d in ds)

        def region_done():
            """The server has worked on version `v` and no longer elaborates the watched lines."""
            ver, prog = self.progress.get(uri, (None, None))
            if ver != v or v not in self.busy_versions.get(uri, ()):
                return False
            return not any(r["range"]["end"]["line"] >= watch[0] and
                           (watch[1] is None or r["range"]["start"]["line"] < watch[1])
                           for r in prog)

        with self.state:
            self.state.wait_for(lambda: self.dead or done.is_set() or
                                (first_error and (has_error() or region_done())))
            stopped_early = not done.is_set()
        if not stopped_early:
            with self.state:
                # diagnostics are complete; the progress report follows them
                self.state.wait_for(lambda: self.dead or (
                    self.progress.get(uri, (None, None))[0] in (v, None)
                    and self.progress.get(uri, (None, [1]))[1] == []), 30)
        with self.state:
            diags = self.diags.get(uri, (v, []))[1]
        if fast:
            mode += ", fast"
        if split:
            mode += ", split %d" % split
        if stopped_early:
            mode += (", stopped at the first error" if has_error() else
                     ", stopped when the edited declaration was done") + \
                " (the server goes on elaborating)"
        out = {"file": path, "mode": mode, "seconds": time.time() - t0, "diagnostics": diags,
               "goals": []}
        lines = text.split("\n")
        for (line, col) in goals:
            if col is None:
                col = len(lines[line - 1]) if 0 < line <= len(lines) else 0
            r = self.request("$/lean/plainGoal", {"textDocument": {"uri": uri},
                                                  "position": {"line": line - 1, "character": col}})
            res = r.get("result")
            out["goals"].append({"line": line, "col": col,
                                 "goals": res.get("goals") if res else None})
        return out

    def evict(self, keep):
        with self.files_lock:
            open_files = [(e["used"], p) for p, e in self.files.items()
                          if p != keep and e["text"] is not None]
        open_files.sort()
        while len(open_files) >= self.max_open:
            _, p = open_files.pop(0)
            self.notify("textDocument/didClose", {"textDocument": {"uri": uri_of(p)}})
            self.files[p]["text"] = None


FAST_OPTIONS = ("set_option debug.skipKernelTC true set_option linter.unusedVariables false "
                "set_option linter.unusedSimpArgs false set_option linter.unreachableTactic false")


# `--split`: the module of the option `abstractBullets`
SPLIT_MODULE = "Proof.AbstractBullets"


def server_text(text, fast, split):
    """`text` as the server gets it: with FAST_OPTIONS (`fast`) and `set_option abstractBullets
    split` (`split` > 0, with the import of SPLIT_MODULE appended to the last import line) on the
    blank line after the imports, so that no line moves; None if there is no such line."""
    if not fast and not split:
        return text
    lines = text.split("\n")
    last_import = None
    is_module = False
    for i, line in enumerate(lines):
        s = line.strip()
        if s == "module":
            is_module = True
        elif s.split()[:1] in (["import"],) or s.startswith(("public import", "private import",
                                                           "meta import", "public meta import")):
            last_import = i
        elif s and not s.startswith(("--", "/-")) and last_import is not None:
            break
    if last_import is None:
        return None
    opts = []
    if fast:
        opts.append(FAST_OPTIONS)
    if split:
        opts.append("set_option abstractBullets %d" % split)
        if not any(SPLIT_MODULE in l.split() for l in file_imports_text(text)):
            lines[last_import] += (" public import " if is_module else " import ") + SPLIT_MODULE
    for i in range(last_import + 1, len(lines)):
        if not lines[i].strip():
            lines[i] = " ".join(opts)
            return "\n".join(lines)
        if not lines[i].strip().startswith("--"):
            return None
    return None


def file_imports_text(text):
    head = []
    for line in text.split("\n"):
        s = line.strip()
        if s.startswith(("import", "public import", "private import", "meta import",
                         "public meta import")) or s == "module" or not s or s.startswith("--"):
            head.append(s)
        elif head and s.startswith("/-"):
            head.append(s)
        else:
            break
    return head


DECL_STARTS = ("theorem", "lemma", "def", "abbrev", "instance", "example", "structure",
               "inductive", "class", "opaque", "axiom", "set_option", "@[", "private", "protected",
               "noncomputable", "/--", "end", "section", "namespace", "open", "variable", "#")


def edited_region(old, new):
    """The 0-based lines [first changed line, start of the next declaration after it) of
    `new`: where an error is a consequence of the edit rather than one already there. A
    declaration starts at column 0 (`DECL_STARTS`); the end is None for the end of the file."""
    a, b = old.split("\n"), new.split("\n")
    first = next((i for i, (x, y) in enumerate(zip(a, b)) if x != y), min(len(a), len(b)))
    for i in range(first + 1, len(b)):
        if b[i].startswith(DECL_STARTS):
            return (first, i)
    return (first, None)


def first_line(processing):
    """The first line (1-based) of the ranges a `$/lean/fileProgress` reports in progress."""
    return 1 + min(r["range"]["start"]["line"] for r in processing)


def uri_of(path):
    return "file://" + os.path.abspath(path)


# --- the background process -------------------------------------------------------------

def daemon(max_open, idle):
    os.makedirs(STATE, exist_ok=True)
    try:
        os.unlink(SOCK)
    except FileNotFoundError:
        pass
    srv = Server(max_open)
    last = [time.time()]
    s = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    s.bind(SOCK)
    s.listen(16)

    def watchdog():
        while True:
            time.sleep(30)
            if time.time() - last[0] > idle * 60:
                os._exit(0)

    threading.Thread(target=watchdog, daemon=True).start()

    def serve(conn):
        try:
            req = json.loads(conn.makefile().readline())
            last[0] = time.time()
            if req["cmd"] == "stop":
                send_reply(conn, {"ok": True})
                srv.proc.kill()
                os._exit(0)
            if req["cmd"] == "status":
                def where(p):
                    prog = srv.progress.get(uri_of(p), (None, []))[1]
                    return " (elaborating line %d)" % first_line(prog) if prog else ""
                send_reply(conn, {"pid": os.getpid(), "open": [
                    os.path.relpath(p, ROOT) + where(p)
                    for p, e in list(srv.files.items()) if e["text"] is not None]})
                return
            if srv.dead:
                srv.files.clear()
                srv.start()
            results = [None] * len(req["files"])

            def one(i, f):
                try:
                    results[i] = srv.check(f, [tuple(g) for g in req["goals"]] if i == 0 else [],
                                           req.get("fast", False), req.get("first_error", False),
                                           req.get("split", 0))
                except Exception as e:  # report, keep serving
                    results[i] = {"file": f, "error": "%s: %s" % (type(e).__name__, e)}

            ts = [threading.Thread(target=one, args=(i, f)) for i, f in enumerate(req["files"])]
            for t in ts:
                t.start()
            for t in ts:
                t.join()
            last[0] = time.time()
            send_reply(conn, {"results": results})
        except Exception as e:
            try:
                send_reply(conn, {"error": "%s: %s" % (type(e).__name__, e)})
            except OSError:
                pass
        finally:
            conn.close()

    while True:
        conn, _ = s.accept()
        threading.Thread(target=serve, args=(conn,), daemon=True).start()


def send_reply(conn, obj):
    conn.sendall((json.dumps(obj) + "\n").encode())


def connect(args, start):
    for attempt in range(600):
        try:
            c = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
            c.connect(SOCK)
            return c
        except (FileNotFoundError, ConnectionRefusedError):
            if not start:
                return None
            if attempt == 0:
                os.makedirs(STATE, exist_ok=True)
                subprocess.Popen([sys.executable, os.path.abspath(__file__), "--daemon",
                                  "--max-open", str(args.max_open), "--idle", str(args.idle)],
                                 cwd=ROOT, stdin=subprocess.DEVNULL, stdout=open(LOG, "ab"),
                                 stderr=subprocess.STDOUT, start_new_session=True)
            time.sleep(0.1)
    sys.exit("lean-check: the background server did not start (see %s)" % LOG)


def call(c, req):
    c.sendall((json.dumps(req) + "\n").encode())
    return json.loads(c.makefile().readline())


# --- output ------------------------------------------------------------------------------

SEVERITY = {1: "error", 2: "warning", 3: "info", 4: "hint"}


def print_result(r, quiet):
    rel = os.path.relpath(r["file"])
    if "error" in r:
        print("%s: lean-check: %s" % (rel, r["error"]))
        return True
    errors = 0
    for d in sorted(r["diagnostics"], key=lambda d: (d["range"]["start"]["line"],
                                                      d["range"]["start"]["character"])):
        sev = SEVERITY.get(d.get("severity", 1), "error")
        errors += sev == "error"
        if quiet and sev != "error":
            continue
        st = d["range"]["start"]
        # (an import's failed build: Lake's command lines say nothing more)
        msg = "\n".join(l for l in d["message"].split("\n") if not l.startswith("trace: "))
        print("%s:%d:%d: %s: %s" % (rel, st["line"] + 1, st["character"], sev, msg))
    for g in r["goals"]:
        print("-- goal at %s:%d:%d" % (rel, g["line"], g["col"]))
        if g["goals"] is None:
            print("(no tactic proof here)")
        elif not g["goals"]:
            print("no goals")
        else:
            print("\n\n".join(g["goals"]))
    print("%s: %s, %.1fs, %d error%s" % (rel, r["mode"], r["seconds"], errors,
                                        "" if errors == 1 else "s"), file=sys.stderr)
    return errors > 0


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("files", nargs="*")
    ap.add_argument("--goal", action="append", default=[], metavar="LINE[:COL]",
                    help="print the goal at this position of the (first) file")
    ap.add_argument("-q", "--quiet", action="store_true", help="only errors")
    ap.add_argument("-e", "--first-error", action="store_true",
                    help="return at the first error, without waiting for the rest of the file")
    ap.add_argument("--split", action="store_true",
                    help="prove each long `·` block as an auxiliary theorem (see above)")
    ap.add_argument("--split-min", type=int, default=20, metavar="N",
                    help="with --split: the blocks of at least N lines (default 20)")
    ap.add_argument("--fast", action="store_true",
                    help="skip the kernel's check and the slower linters (see above)")
    ap.add_argument("--status", action="store_true")
    ap.add_argument("--stop", action="store_true")
    ap.add_argument("--max-open", type=int, default=4)
    ap.add_argument("--idle", type=float, default=60, help="minutes")
    ap.add_argument("--daemon", action="store_true", help=argparse.SUPPRESS)
    args = ap.parse_args()
    if args.daemon:
        daemon(args.max_open, args.idle)
        return
    if args.stop or args.status:
        c = connect(args, start=False)
        if c is None:
            print("lean-check: no server running")
            return
        r = call(c, {"cmd": "stop" if args.stop else "status"})
        if args.status:
            print("server pid %d; open: %s" % (r["pid"], ", ".join(r["open"]) or "nothing"))
        return
    if not args.files:
        ap.error("no files")
    goals = []
    for g in args.goal:
        line, _, col = g.partition(":")
        goals.append((int(line), int(col) if col else None))
    files = []
    for f in args.files:
        if not f.endswith(".lean"):  # a module name
            f = f.replace(".", os.sep) + ".lean"
        if not os.path.exists(f):
            sys.exit("lean-check: no file %s" % f)
        files.append(os.path.abspath(f))
    r = call(connect(args, start=True), {"cmd": "check", "files": files, "goals": goals,
                                               "fast": args.fast,
                                               "split": args.split_min if args.split else 0,
                                               "first_error": args.first_error})
    if "error" in r:
        sys.exit("lean-check: " + r["error"])
    bad = False
    for res in r["results"]:
        bad |= print_result(res, args.quiet)
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
