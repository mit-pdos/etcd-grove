"""Loading trace directories in the tracer's format (examples/net/conform/README.md, "The trace
format", version 1): one `.jsonl` file per process, a node's or a driver's. A run is one
directory; a `.tar.gz` (the committed sample) may hold several.
"""

import collections
import io
import json
import os
import tarfile

VERSION = 1


class Call:
    """One call: its `B` record and its `E` record (None: it had not returned when its process
    ended)."""
    __slots__ = ("proc", "s", "g", "op", "id", "b", "e")

    def __init__(self, proc, b):
        self.proc, self.b, self.e = proc, b, None
        self.s, self.g, self.op, self.id = b["s"], b.get("g"), b["op"], b.get("id")

    @property
    def call(self):
        return self.b["t"]

    @property
    def ret(self):
        return self.e["t"] if self.e is not None else None

    def where(self):
        return f"{self.proc.tag}#{self.s}"

    def sock(self):
        """The socket's global name (pid, id), or None."""
        return (self.proc.pid, self.id) if self.id is not None else None

    def new(self):
        """The socket a successful call returned, or None."""
        if self.e is None:
            return None
        return self.e.get("new")


class Proc:
    def __init__(self, name):
        self.file = name
        self.header = None
        self.role = None
        self.pid = None
        self.node = None
        self.calls = []
        self.events = []   # a driver's P records
        self.truncated = 0
        self.tag = name

    @property
    def first_t(self):
        ts = [c.call for c in self.calls]
        return min(ts) if ts else None

    @property
    def last_t(self):
        ts = [c.call for c in self.calls] + [c.ret for c in self.calls if c.ret is not None]
        return max(ts) if ts else None


class Run:
    def __init__(self, name):
        self.name = name
        self.procs = []     # node processes
        self.drivers = []   # driver processes
        self.pevents = {}   # child pid -> {"start": rec, "kill": rec, "exit": rec}
        self.problems = []  # format problems


def _parse(name, text):
    p = Proc(name)
    lines = text.split("\n")
    if lines and lines[-1] == "":
        lines.pop()
    byseq = {}
    for i, line in enumerate(lines):
        try:
            r = json.loads(line)
        except json.JSONDecodeError:
            if i == len(lines) - 1:
                p.truncated += 1  # a record cut short by a kill
                continue
            raise ValueError(f"{name}: line {i + 1} is not JSON")
        k = r.get("k")
        if i == 0:
            if k != "H":
                raise ValueError(f"{name}: the first line is not a header")
            if r.get("v") != VERSION:
                raise ValueError(f"{name}: format version {r.get('v')}, this checker reads {VERSION}")
            p.header = r
            p.role = r.get("role")
            p.pid = r.get("pid")
            p.node = r.get("node")
            continue
        if k == "B":
            c = Call(p, r)
            byseq[r["s"]] = c
            p.calls.append(c)
        elif k == "E":
            c = byseq.get(r["s"])
            if c is None:
                raise ValueError(f"{name}: E record #{r['s']} with no B record")
            c.e = r
        elif k == "P":
            p.events.append(r)
    if p.role == "node":
        p.tag = f"{p.node}/{p.pid}"
    else:
        p.tag = f"driver:{p.node}/{p.pid}"
    return p


def _finish(run):
    for d in run.drivers:
        for ev in d.events:
            run.pevents.setdefault(ev["cpid"], {})[ev["ev"]] = ev
    run.procs.sort(key=lambda p: (p.header.get("t0", 0), p.pid))
    return run


def load_dir(path):
    run = Run(path)
    for name in sorted(os.listdir(path)):
        if not name.endswith(".jsonl"):
            continue
        with open(os.path.join(path, name), encoding="utf-8") as fp:
            p = _parse(os.path.join(path, name), fp.read())
        (run.procs if p.role == "node" else run.drivers).append(p)
    return _finish(run)


def load_targz(path):
    """Every directory of a .tar.gz with .jsonl files in it, as a run (named after it)."""
    byd = collections.defaultdict(list)
    with tarfile.open(path, "r:gz") as tf:
        for m in tf.getmembers():
            if m.isfile() and m.name.endswith(".jsonl"):
                text = tf.extractfile(m).read().decode("utf-8")
                byd[os.path.dirname(m.name)].append((m.name, text))
    runs = []
    for d in sorted(byd):
        run = Run(f"{path}:{d}")
        for name, text in sorted(byd[d]):
            p = _parse(name, text)
            (run.procs if p.role == "node" else run.drivers).append(p)
        runs.append(_finish(run))
    return runs


def run_dirs(path):
    """The run directories under path (path itself if it holds .jsonl files)."""
    out = []
    for root, dirs, files in os.walk(path):
        dirs.sort()
        if any(f.endswith(".jsonl") for f in files):
            out.append(root)
    return out


def load_any(path):
    if path.endswith(".tar.gz"):
        return load_targz(path)
    return [load_dir(d) for d in run_dirs(path)]
