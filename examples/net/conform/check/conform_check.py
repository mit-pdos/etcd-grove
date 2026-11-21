#!/usr/bin/env python3
"""The conformance checker's command (README.md, "Running it").

  conform_check.py check PATH... [--witness DIR] [--calls-out DIR] [-v]
      check each run (a trace directory, a directory of them, or a .tar.gz of the sample);
      exit 0 if every run is ADMITTED or OUT OF SCOPE with no finding, 2 if one is NOT ADMITTED;
      --calls-out writes each run's processes and calls, verbatim, for the Lean replay
      (`lake exe net-replay`; README.md, "Certification in Lean")
  conform_check.py table PATH... [--json FILE]
      check every run under PATH and print one line per run: verdict, time, sizes
  conform_check.py mutate PATH... [-n N] [--seed S]
      the mutation check (mutate.py): every mutant must be NOT ADMITTED
"""

import argparse
import json
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import checker  # noqa: E402
import trace as T  # noqa: E402


def _runs(paths):
    for p in paths:
        if p.endswith(".tar.gz"):
            yield from T.load_targz(p)
        else:
            for d in T.run_dirs(p):
                t0 = time.monotonic()
                r = T.load_dir(d)
                r.load_seconds = time.monotonic() - t0
                yield r


def _wname(run):
    return run.name.replace("/", "_").replace(":", "_").strip("_") + ".witness.json"


def calls_json(run):
    """The run as the Lean replay reads it (README.md, "Certification in Lean", the calls file):
    every node process (its header's pid, node, t0, t1 and timens, and its driver's exit event's
    time, if any), every driver (pid, node, timens: the exit events' clock) and every call (its B
    and E records as the tracer wrote them; E null if the call never returned). Nothing is mapped
    or interpreted here: the replay applies the mapping itself."""
    procs = []
    for p in run.procs:
        h = p.header
        ex = run.pevents.get(p.pid, {}).get("exit")
        procs.append({"pid": p.pid, "node": p.node, "t0": h.get("t0"), "t1": h.get("t1"),
                      "timens": h.get("timens"), "exit": ex["t"] if ex is not None else None})
    drivers = [{"pid": d.pid, "node": d.node, "timens": d.header.get("timens")} for d in run.drivers]
    calls = [{"pid": c.proc.pid, "b": c.b, "e": c.e} for p in run.procs for c in p.calls]
    return {"format": "net-calls", "version": 1, "run": run.name, "procs": procs,
            "drivers": drivers, "calls": calls}


def cmd_check(a):
    bad = 0
    for run in _runs(a.paths):
        res = checker.check_run(run, limit=a.limit, replay=not a.no_replay)
        print(checker.report(res, verbose=a.verbose))
        if res["verdict"] == "NOT ADMITTED":
            bad += 1
        if a.witness and res["witness"] is not None:
            os.makedirs(a.witness, exist_ok=True)
            with open(os.path.join(a.witness, _wname(run)), "w") as fp:
                json.dump(res["witness"], fp)
        if a.calls_out:
            os.makedirs(a.calls_out, exist_ok=True)
            with open(os.path.join(a.calls_out, _wname(run)[:-len(".witness.json")] + ".calls.json"), "w") as fp:
                json.dump(calls_json(run), fp)
    return 2 if bad else 0


def witness_stats(w):
    """What the witness used of the model's nondeterminism."""
    if w is None:
        return {}
    steps = w["steps"]
    return {"steps": len(steps),
            "crashes": sum(1 for s in steps if s["op"] == "Crash"),
            "cuts": sum(1 for s in steps if s.get("cut")),
            "retro_cuts": w["retro_cuts"],
            "abandoned": sum(1 for s in steps if s["op"] == "Dial" and "abandoned" in s["res"]),
            "multistep": sum(1 for s in steps if s["op"] == "Write" and s.get("part") == 1),
            "unfinished": sum(1 for s in steps if s.get("pending"))}


def cmd_table(a):
    rows = []
    for run in _runs(a.paths):
        res = checker.check_run(run, limit=a.limit, replay=not a.no_replay)
        st = res["stats"]
        calls = sum(v for k, v in st.items() if k.startswith("calls "))
        hard = [f for f in res["findings"] if f.kind in checker.HARD]
        scope = [f for f in res["findings"] if f.kind in ("scope", "inconclusive")]
        w = res["witness"]
        row = {"run": run.name, "verdict": res["verdict"], "load_s": round(getattr(run, "load_seconds", 0.0), 2),
               "check_s": round(res["seconds"], 2), "processes": st.get("processes", 0), "calls": calls,
               "conns": st.get("components: connections", 0), "findings": len(hard), "scope": len(scope),
               "first": (hard[0].where + ": " + hard[0].what) if hard else (scope[0].what if scope else "")}
        row.update(witness_stats(w))
        rows.append(row)
        ws = (f" | witness {row['steps']} steps, {row['crashes']} crashes, {row['cuts']} cuts "
              f"({row['retro_cuts']} retro), {row['abandoned']} D16, {row['multistep']} multi-step Writes, "
              f"{row['unfinished']} unfinished"
              if w else "")
        print(f"{row['verdict']:13} {row['load_s']:6.2f}s {row['check_s']:6.2f}s {row['processes']:4} procs "
              f"{row['calls']:6} calls {row['conns']:5} conns  {run.name}{ws}", flush=True)
        if hard or a.verbose:
            print(checker.report(res, verbose=a.verbose))
    if a.json:
        with open(a.json, "w") as fp:
            json.dump(rows, fp, indent=1)
    return 2 if any(r["verdict"] == "NOT ADMITTED" for r in rows) else 0


def cmd_mutate(a):
    import mutate
    tot = rej = 0
    for run in _runs(a.paths):
        v = checker.check_run(run, replay=False)["verdict"]
        if v != "ADMITTED":
            print(f"{run.name}: {v}, not mutated (only admitted runs are)")
            continue
        res, missed = mutate.run(run, n=a.n, seed=a.seed)
        for kind, (t, r) in sorted(res.items()):
            print(f"{run.name}: {kind}: {r}/{t} rejected")
            tot += t
            rej += r
        for m in missed:
            print(f"  ADMITTED (missed): {m}")
    print(f"total: {rej}/{tot} mutants rejected ({100.0 * rej / max(tot, 1):.1f}%)")
    return 0 if rej == tot else 2


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    for name in ("check", "table", "mutate"):
        p = sub.add_parser(name)
        p.add_argument("paths", nargs="+")
        p.add_argument("--limit", type=int, default=5_000_000, help="search steps per component")
        p.add_argument("--no-replay", action="store_true", help="do not build and replay the witness")
        p.add_argument("-v", "--verbose", action="store_true")
        if name == "check":
            p.add_argument("--witness", help="write each admitted run's witness (JSON) into this directory")
            p.add_argument("--calls-out", help="write each run's processes and calls (JSON) into this directory")
        if name == "table":
            p.add_argument("--json", help="also write the rows as JSON")
        if name == "mutate":
            p.add_argument("-n", type=int, default=5, help="mutants of each kind per run")
            p.add_argument("--seed", type=int, default=1)
    a = ap.parse_args()
    return {"check": cmd_check, "table": cmd_table, "mutate": cmd_mutate}[a.cmd](a)


if __name__ == "__main__":
    sys.exit(main())
