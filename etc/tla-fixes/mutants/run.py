"""Mutation testing of the corrected etcdraft.tla (etc/tla-fixes/README.md).

    python3 run.py RAFT_DIR [MUTANT...]

RAFT_DIR: a raft checkout with the series applied and raft/tla_random_test.go copied in
(check.sh prepares one). Each mutant (mutants.py) is applied to a copy of it, and
TestTLARandom's traces are validated against the copy's tla/. Environment: TLA_TOOLS
(required), SEEDS (default 20), STEPS (default 600), TLA_FEATURES (default: all),
OUT (a JSON file for the results).
"""
import json, os, re, shutil, subprocess, sys, tempfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from mutants import MUTANTS

base = os.path.abspath(sys.argv[1])
names = sys.argv[2:] or list(MUTANTS)
res = {}
for name in names:
    f, old, new, kind, desc = MUTANTS[name]
    with tempfile.TemporaryDirectory() as tmp:
        d = os.path.join(tmp, "raft")
        shutil.copytree(base, d, ignore=shutil.ignore_patterns(".git"))
        p = os.path.join(d, f)
        src = open(p).read()
        assert src.count(old) == 1, (name, src.count(old))
        open(p, "w").write(src.replace(old, new))
        env = dict(os.environ, TLA_SEEDS=os.environ.get("SEEDS", "20"),
                   TLA_STEPS=os.environ.get("STEPS", "600"))
        out = subprocess.run(["go", "test", "-tags", "with_tla", ".", "-run", "^TestTLARandom$",
                              "-count=1", "-v", "-timeout", "120m"],
                             cwd=d, env=env, capture_output=True, text=True).stdout
    rej = len(re.findall(r"seed \d+ \(\d+ lines\): rejected", out))
    pan = len(re.findall(r"seed \d+: raft panicked", out))
    acc = len(re.findall(r"seed \d+ \(\d+ lines\): accepted", out))
    first = re.search(r"seed \d+ .*(rejected|panicked).*", out)
    res[name] = dict(kind=kind, rejected=rej, panicked=pan, accepted=acc,
                     first=first.group(0)[:300] if first else "")
    print(f"{name:32} {kind:7} rejected {rej:3} panicked {pan:3} accepted {acc:3}", flush=True)
if os.environ.get("OUT"):
    json.dump(res, open(os.environ["OUT"], "w"), indent=1)
