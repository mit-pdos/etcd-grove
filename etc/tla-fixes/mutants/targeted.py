"""Runs raft/tla_targeted_test.go's schedules against each mutant (mutants.py).

    python3 targeted.py RAFT_DIR

RAFT_DIR as for run.py (with raft/tla_targeted_test.go copied in). Prints, per mutant, which
schedules' traces TLC rejected (FAIL) and which it accepted (PASS). Needs TLA_TOOLS.
"""
import os, re, shutil, subprocess, sys, tempfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from mutants import MUTANTS

base = os.path.abspath(sys.argv[1])
for name, (f, old, new, kind, desc) in MUTANTS.items():
    with tempfile.TemporaryDirectory() as tmp:
        d = os.path.join(tmp, "raft")
        shutil.copytree(base, d, ignore=shutil.ignore_patterns(".git"))
        p = os.path.join(d, f)
        src = open(p).read()
        assert src.count(old) == 1, name
        open(p, "w").write(src.replace(old, new))
        out = subprocess.run(["go", "test", "-tags", "with_tla", ".", "-run", "^TestTLATargeted",
                              "-count=1", "-v"], cwd=d, capture_output=True, text=True).stdout
    res = re.findall(r"--- (PASS|FAIL): TestTLATargeted(\w+)", out)
    print(f"{name:32} {kind:7} " + " ".join(f"{t}={r}" for r, t in res), flush=True)
