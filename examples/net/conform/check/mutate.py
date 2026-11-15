"""The mutation check (as dsverify-lab's harness/conform/mutate.py): mutants of real runs, each a
trace no execution of the model produces; the checker must reject (NOT ADMITTED) every one. This
shows that the real runs exercise the rules: a vacuous checker would admit the mutants.

  m-flip        a successful Read's bytes, one byte changed (ReadAvail: the next unread bytes)
  m-short       a successful Write of n > 0 bytes reports n - 1, with no error (WriteOutcome: all)
  m-closeerr    a successful Close returns a sys error (CloseOutcome, D17: it succeeds)
  m-liscloseerr a successful listener Close returns a sys error (LisCloseOutcome, D17)
  m-readclosed  a Read added after a successful Close of the same end, returning io.EOF
                (ReadOutcome: a closed end gives only `closed`)
  m-swap        two successive successful Reads of one end, their bytes swapped (where that
                changes the stream: TcpDir.bytes is a queue)
  m-early       a successful Read with bytes moved before every other call
  m-timeout     a successful Read at an end that never set a deadline returns a timeout (ReadAvail:
                `st.rdl = true`)
  m-closedopen  a successful Read at an end no Close of which began before it returned returns
                ErrClosed (ReadOutcome: only on a closed end)
  m-dialshape   a failed plain Dial's error becomes a deadline error (Dial.impl: `kindErr` of the
                extension's code, and DialStep fails only with sys)
"""

import copy
import random

import checker
from tracebuild import EOF, err_closed, err_timeout

KINDS = ["m-flip", "m-short", "m-closeerr", "m-liscloseerr", "m-readclosed", "m-swap", "m-early",
         "m-timeout", "m-closedopen", "m-dialshape"]


def _calls(run):
    for p in run.procs:
        for c in p.calls:
            yield c


def _candidates(run):
    cands = {k: [] for k in KINDS}
    deadline_ends = {c.sock() for c in _calls(run) if c.op == "SetDeadline"}
    close_begin = {}
    for c in _calls(run):
        if c.op == "Close":
            close_begin.setdefault(c.sock(), []).append(c.call)
    reads = {}
    for c in _calls(run):
        if c.e is None:
            continue
        err = c.e.get("err")
        if c.op == "Read" and err is None and c.e.get("data"):
            cands["m-flip"].append(c)
            cands["m-early"].append(c)
            if c.sock() not in deadline_ends:
                cands["m-timeout"].append(c)
            if not any(t < c.ret for t in close_begin.get(c.sock(), [])):
                cands["m-closedopen"].append(c)
            reads.setdefault(c.sock(), []).append(c)
        if c.op == "Write" and err is None and c.e.get("n", 0) > 0:
            cands["m-short"].append(c)
        if c.op == "Close" and err is None:
            cands["m-closeerr"].append(c)
            cands["m-readclosed"].append(c)
        if c.op == "ListenerClose" and err is None:
            cands["m-liscloseerr"].append(c)
        if c.op == "Dial" and err is not None and err.get("inner") == "*os.SyscallError":
            cands["m-dialshape"].append(c)
    for sock, rs in reads.items():
        rs.sort(key=lambda c: c.call)
        for x, y in zip(rs, rs[1:]):
            dx, dy = x.e["data"], y.e["data"]
            if x.ret < y.call and dx + dy != dy + dx:
                cands["m-swap"].append((x, y))
    return cands


def _key(c):
    return (c.proc.pid, c.s)


def _find(run, key):
    for c in _calls(run):
        if (c.proc.pid, c.s) == key:
            return c
    raise KeyError(key)


def mutants(run, rng, n):
    """Yield (kind, description, mutated run), up to n of each kind."""
    cands = _candidates(run)
    tmin = min(c.call for c in _calls(run))
    for kind in KINDS:
        lst = cands[kind]
        rng.shuffle(lst)
        for item in lst[:n]:
            m = copy.deepcopy(run)
            if kind == "m-swap":
                x, y = _find(m, _key(item[0])), _find(m, _key(item[1]))
                x.e["data"], y.e["data"] = y.e["data"], x.e["data"]
                x.e["n"], y.e["n"] = y.e["n"], x.e["n"]
                yield kind, f"{x.where()},{y.where()}: Read bytes swapped", m
                continue
            c = _find(m, _key(item))
            if kind == "m-flip":
                d = bytearray(bytes.fromhex(c.e["data"]))
                i = rng.randrange(len(d))
                d[i] ^= 0x01
                c.e["data"] = d.hex()
                desc = f"{c.where()}: Read byte {i} changed"
            elif kind == "m-short":
                c.e["n"] -= 1
                desc = f"{c.where()}: Write n={c.e['n']} of {c.b['n']}, no error"
            elif kind in ("m-closeerr", "m-liscloseerr"):
                op = "Close" if kind == "m-closeerr" else "ListenerClose"
                c.e["err"] = {**err_closed(op), "inner": "*os.SyscallError", "isClosed": False,
                              "syscall": "close", "errno": 9}
                desc = f"{c.where()}: {op} returns EBADF"
            elif kind == "m-readclosed":
                p = c.proc
                t = c.ret + 1
                seq = max(x.s for x in p.calls) + 1
                b = {"k": "B", "pid": p.pid, "node": p.node, "s": seq, "g": c.g, "op": "Read", "id": c.id,
                     "n": 16, "t": t}
                nc = type(c)(p, b)
                nc.e = {"k": "E", "pid": p.pid, "node": p.node, "s": seq, "g": c.g, "op": "Read", "id": c.id,
                        "t": t + 1, "n": 0, "err": EOF}
                p.calls.append(nc)
                desc = f"{nc.where()}: a Read of {c.id} after its Close {c.where()} returns io.EOF"
            elif kind == "m-early":
                c.b["t"], c.e["t"] = tmin - 10, tmin - 5
                desc = f"{c.where()}: a Read moved before every other call"
            elif kind == "m-timeout":
                c.e["err"] = err_timeout("Read")
                c.e["n"] = 0
                c.e.pop("data", None)
                desc = f"{c.where()}: a Read times out with no deadline set"
            elif kind == "m-closedopen":
                c.e["err"] = err_closed("Read")
                c.e["n"] = 0
                c.e.pop("data", None)
                desc = f"{c.where()}: a Read at an open end returns ErrClosed"
            elif kind == "m-dialshape":
                c.e["err"] = err_timeout("Dial")
                desc = f"{c.where()}: a plain Dial fails with a deadline error"
            yield kind, desc, m


def run(r, n=5, seed=1, plan=None):
    """Mutants of the run r; returns ({kind: (made, rejected)}, [descriptions of the admitted])."""
    rng = random.Random(seed)
    res = {}
    missed = []
    for kind, desc, m in mutants(r, rng, n):
        v = checker.check_run(m, plan=plan, replay=False)["verdict"]
        made, rej = res.get(kind, (0, 0))
        res[kind] = (made + 1, rej + (v == "NOT ADMITTED"))
        if v != "NOT ADMITTED":
            missed.append(f"{r.name}: {kind}: {desc} ({v})")
    return res, missed
