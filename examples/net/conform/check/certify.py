#!/usr/bin/env python3
"""Certification in Lean (README.md, "Certification in Lean"): run the checker on runs, write
each admitted run's witness and calls, and replay them through the Lean replay
(`lake exe net-replay`, GooseLang/Ext/Net/Replay.lean); every admitted run must be CERTIFIED.
Then the negative tests: tampered witnesses of the sample, each NOT CERTIFIED at the step (or the
call) the tampering touched.

  certify.py [PATH...] [--exe EXE] [--out DIR] [--no-negative] [--json FILE]

PATH: runs as conform_check.py takes them (default: the sample, ../testdata/*.tar.gz). EXE: the
replay (default: the repository's .lake/build/bin/net-replay; build it with
`lake build net-replay`). DIR: where the witnesses and calls go (default: a fresh temporary
directory, removed after). Exits 0 if every admitted run is CERTIFIED, every OUT OF SCOPE run that
has a witness is NOT CERTIFIED (the replay certifies only runs wholly in the model), and every
negative test is rejected where expected; 1 otherwise.
"""

import argparse
import copy
import glob
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import checker  # noqa: E402
import conform_check as CC  # noqa: E402

ROOT = os.path.normpath(os.path.join(HERE, "..", "..", "..", ".."))
EXE = os.path.join(ROOT, ".lake", "build", "bin", "net-replay")
TESTDATA = os.path.join(HERE, "..", "testdata")


def replay(exe, wpath, cpath):
    """Run the Lean replay: (certified, the step it failed at or None, its output, seconds)."""
    t0 = time.monotonic()
    p = subprocess.run([exe, wpath, cpath], capture_output=True, text=True)
    dt = time.monotonic() - t0
    out = (p.stdout + p.stderr).strip()
    if p.returncode == 0 and out.startswith("CERTIFIED"):
        return True, None, out, dt
    if p.returncode != 1 or not out.startswith("NOT CERTIFIED"):
        raise RuntimeError(f"{exe} {wpath}: exit {p.returncode}: {out}")
    m = re.match(r"NOT CERTIFIED: step (\d+):", out)
    return False, (int(m.group(1)) if m else None), out, dt


def write_pair(out, run, witness, calls=None):
    base = os.path.join(out, CC._wname(run)[:-len(".witness.json")])
    with open(base + ".witness.json", "w") as fp:
        json.dump(witness, fp)
    with open(base + ".calls.json", "w") as fp:
        json.dump(calls if calls is not None else CC.calls_json(run), fp)
    return base + ".witness.json", base + ".calls.json"


def certify(paths, exe, out, rows):
    ok = True
    for run in CC._runs(paths):
        t0 = time.monotonic()
        res = checker.check_run(run)
        tcheck = time.monotonic() - t0
        v, w = res["verdict"], res["witness"]
        row = {"run": run.name, "verdict": v, "load_s": round(getattr(run, "load_seconds", 0.0), 2),
               "check_s": round(tcheck, 2)}
        if w is None:
            row["lean"] = "-"
            print(f"{v:13} {run.name}: no witness", flush=True)
            if v == "ADMITTED":
                ok = False
            rows.append(row)
            continue
        wp, cp = write_pair(out, run, w)
        cert, step, msg, dt = replay(exe, wp, cp)
        row.update(lean="CERTIFIED" if cert else "NOT CERTIFIED", lean_s=round(dt, 2), steps=len(w["steps"]),
                   witness_mb=round(os.path.getsize(wp) / 1e6, 1), calls_mb=round(os.path.getsize(cp) / 1e6, 1),
                   lean_out=msg)
        rows.append(row)
        good = cert if v == "ADMITTED" else not cert
        ok = ok and good
        print(f"{v:13} {run.name}: Lean {msg}{'' if good else '   <-- UNEXPECTED'}", flush=True)
    return ok


# ---------------------------------------------------------------------------------------------
# Negative tests: tampered witnesses of the sample

def _load(name):
    runs = CC._runs([os.path.join(TESTDATA, name)])
    run = next(iter(runs))
    res = checker.check_run(run)
    assert res["verdict"] == "ADMITTED", (name, res["verdict"])
    return run, res["witness"]


def _steps(w, **kw):
    return [s for s in w["steps"] if all(s.get(k) == v for k, v in kw.items())]


def _calls_of(run):
    return {(c.proc.pid, c.s): c for p in run.procs for c in p.calls}


def tampers():
    """(name, run, tampered witness, tampered calls (None: the run's), the step it must fail at
    (None: a call), a substring of the expected message)."""
    out = []
    run, w = _load("probe-dialthenlisten.tar.gz")
    calls = _calls_of(run)

    # a wrong k: the Write of "hi" counted as 1 byte (the loop then goes on, last is wrong)
    t = copy.deepcopy(w)
    s = _steps(t, op="Write")[0]
    s["res"]["k"] = 1
    out.append(("wrong Write k", run, t, None, s["i"], "loop goes on"))

    # a wrong Read k: the Read of "hi" says 1 byte but has both
    t = copy.deepcopy(w)
    s = [x for x in _steps(t, op="Read") if x["res"]["code"] == 0][0]
    s["res"]["k"] = 1
    out.append(("wrong Read k", run, t, None, s["i"], "k is not its bytes' count"))

    # a Read of other bytes than the trace's (one byte of two, the other left in the direction)
    t = copy.deepcopy(w)
    s = [x for x in _steps(t, op="Read") if x["res"]["code"] == 0][0]
    s["res"]["k"], s["res"]["data"] = 1, s["res"]["data"][:2]
    out.append(("bytes read short", run, t, None, s["i"], "other bytes"))

    # a forged EOF: the Read that returned "hi" reads EOF (no cut)
    t = copy.deepcopy(w)
    s = [x for x in _steps(t, op="Read") if x["res"]["code"] == 0][0]
    s["res"] = {"code": 4}
    out.append(("forged EOF", run, t, None, s["i"], "ReadOutcome"))

    # a forged EOF that the model allows (a cut keeping nothing) but the trace did not see
    t = copy.deepcopy(w)
    s = [x for x in _steps(t, op="Read") if x["res"]["code"] == 0][0]
    s["res"], s["cut"] = {"code": 4}, {"keep": 0}
    out.append(("forged EOF (with a cut)", run, t, None, s["i"], "result code 4"))

    # a wrong error kind: the Accept on the closed listener fails sys instead of closed
    t = copy.deepcopy(w)
    s = [x for x in _steps(t, op="Accept") if x["res"]["code"] == 1][0]
    s["res"]["code"] = 3
    out.append(("wrong error kind (Accept)", run, t, None, s["i"], "AcceptStep"))

    # a wrong error kind: the listener's first Close fails closed (LisCloseOutcome: only on a
    # closed listener)
    t = copy.deepcopy(w)
    s = [x for x in _steps(t, op="LisClose") if x["res"]["code"] == 0][0]
    s["res"]["code"] = 1
    out.append(("wrong error kind (LisClose)", run, t, None, s["i"], "LisCloseOutcome"))

    # bytes never written, the trace and the witness agreeing on them: only the model refuses
    t = copy.deepcopy(w)
    cl = copy.deepcopy(CC.calls_json(run))  # its records are the run's
    s = [x for x in _steps(t, op="Read") if x["res"]["code"] == 0][0]
    s["res"]["data"] = "6868"
    for c in cl["calls"]:
        if (c["pid"], c["b"]["s"]) == (s["trace"]["pid"], s["trace"]["s"]):
            c["e"]["data"] = "6868"
    out.append(("bytes never written", run, t, cl, s["i"], "not a step of the model: Read"))

    # a call out of the model's scope (an unmodeled API): a certified run is wholly in the model
    cl = copy.deepcopy(CC.calls_json(run))
    c0 = cl["calls"][0]
    cl["calls"].append({"pid": c0["pid"], "e": None, "b": {
        "k": "B", "pid": c0["pid"], "s": 999, "op": "Unmodeled", "api": "TCPConn.SetNoDelay", "id": "c2",
        "t": c0["b"]["t"]}})
    out.append(("out-of-scope call", run, copy.deepcopy(w), cl, None, "out of scope"))

    # a Go error net.lean cannot build: the closed listener's Accept error with Timeout() true
    cl = copy.deepcopy(CC.calls_json(run))
    s = [x for x in _steps(w, op="Accept") if x["res"]["code"] == 1][0]
    for c in cl["calls"]:
        if (c["pid"], c["b"]["s"]) == (s["trace"]["pid"], s["trace"]["s"]):
            c["e"]["err"]["timeout"] = True
    out.append(("error shape (closed, Timeout true)", run, copy.deepcopy(w), cl, None, "Timeout() or Temporary() true"))

    # the mapping: a plain Dial's deadline error is the kind timeout, which the witness's sys
    # failure is not (and DialStep never returns)
    cl = copy.deepcopy(CC.calls_json(run))
    s = [x for x in _steps(w, op="Dial") if x["res"]["code"] == 3][0]
    for c in cl["calls"]:
        if (c["pid"], c["b"]["s"]) == (s["trace"]["pid"], s["trace"]["s"]):
            c["e"]["err"].update({"inner": "*poll.DeadlineExceededError", "timeout": True, "temporary": True,
                                  "isDeadline": True})
            c["e"]["err"].pop("errno", None)
            c["e"]["err"].pop("syscall", None)
    out.append(("Dial deadline error mapped", run, copy.deepcopy(w), cl, s["i"], "maps to 2"))

    # a wrong accepted connection: the Accept returns the connection a later Dial makes
    t = copy.deepcopy(w)
    s = [x for x in _steps(t, op="Accept") if x["res"]["code"] == 0][0]
    s["res"]["conn"], s["res"]["end"] = 2, 5
    out.append(("wrong accepted connection", run, t, None, s["i"], "Accept"))

    # a missing call: the last Dial's step deleted
    t = copy.deepcopy(w)
    last = t["steps"].pop()
    out.append(("missing call", run, t, None, None, f"{last['trace']['pid']}#{last['trace']['s']}"))

    # a step out of its call's interval (after the call returned; still in t order)
    t = copy.deepcopy(w)
    for a, b in zip(t["steps"], t["steps"][1:]):
        c = calls[(a["trace"]["pid"], a["trace"]["s"])]
        if c.e is not None and c.e["t"] + 1 <= b["t"]:
            a["t"] = c.e["t"] + 1
            out.append(("step after its call returned", run, t, None, a["i"], "outside the call's interval"))
            break

    # steps out of t order (two swapped)
    t = copy.deepcopy(w)
    st = t["steps"]
    st[3], st[4] = st[4], st[3]
    out.append(("steps swapped", run, t, None, st[4]["i"], "not in t order"))

    # v3.4 (witness version 2: no plan; a Listen listens at its own address): the addresses are
    # checked at each Listen and Dial step, and at each Accept the listener's address must take
    # the connection's (lisAccepts). The witness and the calls are tampered together, so that the
    # call check agrees and only the model refuses.
    def readdr(t, cl, s, a):
        s["addr"] = a
        for c in cl["calls"]:
            if (c["pid"], c["b"]["s"]) == (s["trace"]["pid"], s["trace"]["s"]):
                c["b"]["addr"] = a

    # a Listen at an invalid address (an ephemeral port: not listenOk, a panic of the model)
    t, cl = copy.deepcopy(w), copy.deepcopy(CC.calls_json(run))
    s = [x for x in _steps(t, op="Listen") if x["res"]["code"] == 0][0]
    readdr(t, cl, s, "127.0.0.1:40000")
    out.append(("Listen of an invalid address", run, t, cl, s["i"], "listenOk"))

    # a Dial of an invalid address (an ephemeral port: not addrOk, a panic of the model)
    t, cl = copy.deepcopy(w), copy.deepcopy(CC.calls_json(run))
    s = [x for x in _steps(t, op="Dial") if x["res"]["code"] == 3][0]
    readdr(t, cl, s, "127.0.0.1:40000")
    out.append(("Dial of an invalid address", run, t, cl, s["i"], "addrOk"))

    # an Accept at a listener whose address does not take the connection's: the Listen moved to
    # another valid port, the connection still dialed to the old one
    t, cl = copy.deepcopy(w), copy.deepcopy(CC.calls_json(run))
    s = [x for x in _steps(t, op="Listen") if x["res"]["code"] == 0][0]
    port = int(s["addr"].rsplit(":", 1)[1])
    readdr(t, cl, s, s["addr"].rsplit(":", 1)[0] + f":{port + 1}")
    acc = [x for x in _steps(t, op="Accept") if x["res"]["code"] == 0 and x["lis"] == s["res"]["lis"]][0]
    out.append(("Accept at another address", run, t, cl, acc["i"], "not at the address"))

    # a crash left out: the restarted server's first step is then of a process that is not its
    # node's current incarnation
    run2, w2 = _load("echo-TestServerCrashes.tar.gz")
    t = copy.deepcopy(w2)
    j = next(k for k, s in enumerate(t["steps"]) if s["op"] == "Crash")
    cr = t["steps"].pop(j)
    nxt = next(s for s in t["steps"][j:] if s.get("trace", {}).get("pid") == cr["between"][1])
    out.append(("crash left out", run2, t, None, nxt["i"], "current incarnation"))

    # a crash moved before the old process's last step
    t = copy.deepcopy(w2)
    j = next(k for k, s in enumerate(t["steps"]) if s["op"] == "Crash")
    prev = max(k for k in range(j) if t["steps"][k].get("trace", {}).get("pid") == t["steps"][j]["between"][0])
    cr = t["steps"].pop(j)
    cr["t"] = t["steps"][prev]["t"]
    t["steps"].insert(prev, cr)
    out.append(("crash too early", run2, t, None, cr["i"], "crash"))

    # a Write split differently from its trace: a multi-step Write's first step's bytes not the
    # call's (one byte dropped from the front)
    run3, w3 = _load("probe-writeclose.tar.gz")
    t = copy.deepcopy(w3)
    s = [x for x in _steps(t, op="Write") if x.get("part") == 1][0]
    s["data"] = s["data"][2:]
    out.append(("Write step of other bytes", run3, t, None, s["i"], "b[nn:]"))
    return out


def negative(exe, out):
    ok = True
    for name, run, t, cl, step, sub in tampers():
        wp, cp = write_pair(out, run, t, cl)
        cert, got, msg, _ = replay(exe, wp, cp)
        good = (not cert) and got == step and sub in msg
        ok = ok and good
        where = f"step {step}" if step is not None else "a call"
        print(f"{'rejected' if good else 'WRONG   '} {name:32} expected at {where}: {msg[:200]}", flush=True)
    return ok


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("paths", nargs="*")
    ap.add_argument("--exe", default=EXE)
    ap.add_argument("--out")
    ap.add_argument("--no-negative", action="store_true")
    ap.add_argument("--json", help="write the rows as JSON")
    a = ap.parse_args()
    if not os.path.exists(a.exe):
        print(f"{a.exe}: no such file (lake build net-replay)")
        return 1
    paths = a.paths or sorted(os.path.relpath(p) for p in glob.glob(os.path.join(TESTDATA, "*.tar.gz")))
    out = a.out or tempfile.mkdtemp(prefix="net-certify-")
    os.makedirs(out, exist_ok=True)
    rows = []
    try:
        t0 = time.monotonic()
        ok = certify(paths, a.exe, out, rows)
        print(f"certified: {sum(r.get('lean') == 'CERTIFIED' for r in rows)} of {len(rows)} runs "
              f"({time.monotonic() - t0:.1f} s in all, Lean {sum(r.get('lean_s', 0) for r in rows):.1f} s)")
        if not a.no_negative:
            ok = negative(a.exe, out) and ok
        if a.json:
            with open(a.json, "w") as fp:
                json.dump(rows, fp, indent=1)
    finally:
        if not a.out:
            shutil.rmtree(out, ignore_errors=True)
    print("OK" if ok else "FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
