#!/usr/bin/env python3
"""The model-as-parameter gate (per-type message models, stage A: the Scope's G, rules 1-7).

Runs `etc/ModelParamCheck.lean` (see its header for the rules) on the root modules of
`etc/tcb-report.py` (every `Link`/`MainLinked`/`Results` module, in the groups
`etc/proof_roots.py` imports together), with the modules declaring a registration added to the
main group, and its selftests (rule 6's negative tests) on the registration modules alone. Then:

- every `hit` not covered (rule 1), `atom` (rule 2), bad `reg` (rules 3, 4) or bad `sat` (rule 7)
  is a failure;
- every axiom a `Sat` theorem rests on (`satax`, already within Lean's allowlist by module and
  shape) must also appear verbatim on an `axiom` line of its `Code/` file (`[v6a]` 4; the `Code/`
  files are the translations `etc/goose.py --check` checks);
- every selftest must behave as declared (refused, or the one that must pass);
- a floor: at least `MIN_REGS` registrations, each with its `Sat` theorem.

    etc/model-param-check.py [--json FILE] [--reuse] [-v]

Never builds: the `.olean`s must be up to date. `$LAKE_OPTS` is passed to `lake`. Run it under a
memory cap (`systemd-run --scope -p MemoryMax=32G`).
"""
import argparse
import collections
import json
import os
import re
import subprocess
import sys

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
sys.dont_write_bytecode = True
sys.path.insert(0, os.path.join(ROOT, "etc"))
import proof_roots  # noqa: E402

MIN_REGS = 36
REG = re.compile(r"(?:grpcReqModelOf|grpcRepModelOf|streamReqModelOf|streamRepModelOf|pbModelOf) GF \S+ = some")


def reg_modules():
    mods = []
    for d in ("Proof", "Spec"):
        for dp, _, fs in os.walk(os.path.join(ROOT, d)):
            for f in fs:
                if f.endswith(".lean"):
                    p = os.path.join(dp, f)
                    s = open(p, encoding="utf-8").read()
                    if re.search(r"^axiom ", s, re.M) and REG.search(s):
                        mods.append(proof_roots.module_of(p))
    return sorted(mods)


def run(json_path):
    env = dict(os.environ)
    env["PATH"] = os.path.expanduser("~/.elan/bin") + os.pathsep + env.get("PATH", "")
    regs = reg_modules()
    runs = proof_roots.lean_runs()
    # the registration modules join the group without part roots (the main tree)
    main = next((r for r in runs if not proof_roots.parts_reached(r[0])), None)
    if main is None:
        runs.append([])
        main = runs[-1]
    main.extend(m for m in regs if m not in main)
    jobs = [(mods, False) for mods in runs] + [(regs, True)]
    with open(json_path + ".tmp", "w") as f:
        for mods, st in jobs:
            f.flush()
            args = ["--selftest"] if st else []
            r = subprocess.run(proof_roots.lake("env", "lean", "--run", "etc/ModelParamCheck.lean",
                                                *proof_roots.lean_args(), *args, *mods),
                               cwd=ROOT, stdout=f, env=env, check=False)
            if r.returncode != 0:
                sys.exit(f"model-param: FAILED: etc/ModelParamCheck.lean exited {r.returncode} on "
                         f"{len(mods)} modules")
    os.replace(json_path + ".tmp", json_path)


def code_line_ok(module, name, cache={}):
    if module.startswith("Perennial."):
        path = os.path.join(proof_roots._perennial_dir(), *module.split(".")) + ".lean"
    else:
        path = proof_roots.path_of(module)
    if path not in cache:
        try:
            cache[path] = open(path, encoding="utf-8").read()
        except OSError:
            cache[path] = ""
    # the declaration is `axiom <short name>` inside the file's namespace
    short = name.split(".")
    for k in range(len(short)):
        # a component may be written `«…»` (a keyword or `_`)
        pat = r"\.".join(rf"(?:{re.escape(c)}|«{re.escape(c)}»)" for c in short[k:])
        if re.search(rf"^axiom {pat}[\s:\[]", cache[path], re.M):
            return True
    return False


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--json", default=os.path.join(ROOT, ".lake/model-param.jsonl"))
    ap.add_argument("--reuse", action="store_true")
    ap.add_argument("-v", action="store_true")
    a = ap.parse_args()
    if not a.reuse:
        run(a.json)
    objs = [json.loads(l) for l in open(a.json) if l.strip().startswith("{")]
    fails = set()
    regs, sats = {}, collections.defaultdict(set)
    axioms = set()
    selftests = []
    for o in objs:
        t = o["t"]
        if t == "axiom":
            axioms.add(o["name"])
        elif t == "hit" and not o["covered"]:
            fails.add(f"rule 1: {o['axiom']}: model binder {o['path']} ({o['type']}) has no registry premise")
        elif t == "atom":
            fails.add(f"rule 2: {o['axiom']}: a registry atom or registered record is received ({o['where']})")
        elif t == "reg":
            if "bad" in o:
                fails.add(f"registration {o['name']}: {o['bad']}")
            else:
                regs[o["name"]] = o
        elif t == "sat":
            if "bad" in o:
                fails.add(f"rule 7: {o['reg']}: {o['bad']}")
            elif "theorem" in o:
                sats[o["reg"]].add(o["theorem"])
        elif t == "satax":
            if o["axiom"] not in ("propext", "Classical.choice", "Quot.sound") and \
                    not code_line_ok(o["module"], o["axiom"]):
                fails.add(f"rule 7: {o['theorem']} rests on {o['axiom']}, not an axiom line of "
                          f"{o['module']}")
        elif t == "selftest":
            selftests.append(o)
    # each refusal must be for its intended reason (a substring of the refusing line)
    why = {"bare model": '"covered":false', "a stray positive": "not a constant",
           "a post yielding a registry atom": '"t":"atom"', "a post yielding a GrpcMethod": "binder m",
           "an axiom equating": "not a constant", "a theorem proved with sorry": '"t":"atom"',
           "a second registration": "a second registration", "a registration with an extra binder":
           "not a registry argument", "a registration with no Sat": "no theorem of type",
           "a Sat theorem resting on a hand-written zero_val": "Foo.zero_val",
           "a request registration keeping the default wireLen": "wireLen"}
    for st in selftests:
        for k, w in why.items():
            if st["name"].startswith(k) and st.get("refused") and w not in st.get("by", ""):
                fails.add(f"selftest refused for another reason: {st['name']} ({st.get('by', '')[:200]})")
        if not st["ok"]:
            fails.add(f"selftest failed: {st['name']} ({st.get('why', st.get('by', ''))})")
    if len(selftests) == 0:
        fails.add("no selftest ran")
    if len(regs) < MIN_REGS:
        fails.add(f"floor: {len(regs)} registrations, at least {MIN_REGS} expected")
    for r in regs:
        if not sats.get(r):
            fails.add(f"rule 7: {r} has no Sat theorem")
    if a.v:
        for o in selftests:
            print(f"  selftest {'ok' if o['ok'] else 'FAILED'}: {o['name']}  [{o.get('by', '')[:160]}]")
    if fails:
        print(f"model-param: FAILED ({len(fails)})")
        for f in sorted(fails):
            print("  " + f)
        sys.exit(1)
    print(f"model-param: ok ({len(axioms)} trusted statements walked, {len(regs)} registrations "
          f"each with its Sat theorem, {len(selftests)} selftests)")


if __name__ == "__main__":
    main()
