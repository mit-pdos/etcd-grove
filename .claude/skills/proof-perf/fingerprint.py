#!/usr/bin/env python3
"""Fingerprint what this repository's proofs say and rest on, and compare two fingerprints.

    .claude/skills/proof-perf/fingerprint.py -o FILE      # of the current build
    .claude/skills/proof-perf/fingerprint.py --diff OLD NEW

The fingerprint (`fingerprint.lean`) is one line per root theorem (every theorem of a
`Link.lean` or `Results.lean`: its statement), per definition of this repository those
statements reach through types and definition bodies (its type and body), and per axiom
declared in this repository (its type), each with a structural hash.  A change that only
makes proofs faster leaves it unchanged; `--diff` exits 1, listing the lines that differ,
if a statement, a definition it is written in terms of or an axiom changed, appeared or
disappeared.

Run from the root of a checkout whose build is up to date (it never builds: like
`etc/tcb-report.py`, it exits asking for `lake build` if the root modules are stale).
`$LAKE_OPTS` is passed to lake.
"""

import argparse
import os
import subprocess
import sys

sys.dont_write_bytecode = True
ROOT = os.getcwd()
if not os.path.exists(os.path.join(ROOT, "etc", "proof_roots.py")):
    sys.exit("fingerprint.py: run it from the root of an etcd-grove checkout")
sys.path.insert(0, os.path.join(ROOT, "etc"))
import proof_roots  # noqa: E402

LEAN = os.path.join(os.path.dirname(os.path.abspath(__file__)), "fingerprint.lean")


def compute(out_path):
    env = dict(os.environ)
    env["PATH"] = os.path.expanduser("~/.elan/bin") + os.pathsep + env.get("PATH", "")
    proof_roots.check_built("fingerprint.py", env)
    lines = set()
    for mods in proof_roots.lean_runs():
        r = subprocess.run(
            proof_roots.lake("env", "lean", "--run", LEAN, *proof_roots.lean_args(), *mods),
            cwd=ROOT, env=env, capture_output=True, text=True, check=False,
        )
        if r.returncode != 0:
            sys.exit(f"fingerprint.py: fingerprint.lean {' '.join(mods)} failed "
                     f"(exit {r.returncode}):\n{r.stderr[-4000:]}")
        lines.update(l for l in r.stdout.splitlines() if l)
    with open(out_path, "w", encoding="utf-8") as f:
        f.write(f"# head {proof_roots.git_head()}\n")
        for l in sorted(lines):
            f.write(l + "\n")
    kinds = {}
    for l in lines:
        kinds[l.split("\t")[0]] = kinds.get(l.split("\t")[0], 0) + 1
    print(f"{out_path}: " + ", ".join(f"{v} {k}" for k, v in sorted(kinds.items())))


def read(path):
    with open(path, encoding="utf-8") as f:
        rows = [l.rstrip("\n").split("\t") for l in f if l.strip() and not l.startswith("#")]
    return {(k, n): h for k, n, h in rows}


def diff(old_path, new_path):
    old, new = read(old_path), read(new_path)
    changed = sorted(k for k in old.keys() & new.keys() if old[k] != new[k])
    gone = sorted(old.keys() - new.keys())
    added = sorted(new.keys() - old.keys())
    for tag, keys in (("changed", changed), ("removed", gone), ("added", added)):
        for kind, name in keys:
            print(f"{tag}\t{kind}\t{name}")
    n = len(changed) + len(gone) + len(added)
    print(f"fingerprint: {len(old)} -> {len(new)} lines; {len(changed)} changed, "
          f"{len(gone)} removed, {len(added)} added", file=sys.stderr)
    return 1 if n else 0


def main():
    p = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    g = p.add_mutually_exclusive_group(required=True)
    g.add_argument("-o", metavar="FILE", help="fingerprint the current build into FILE")
    g.add_argument("--diff", nargs=2, metavar=("OLD", "NEW"), help="compare two fingerprints")
    a = p.parse_args()
    if a.o:
        compute(a.o)
        return 0
    return diff(*a.diff)


if __name__ == "__main__":
    sys.exit(main())
