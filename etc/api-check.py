#!/usr/bin/env python3
"""Check that a package's clients use its proof only through its signature.

A package with a signature (`Spec/<pkg>/Sig.lean`, `Proof/<pkg>/Sig.lean`: the specs a
client may use, the vocabulary it may name and the laws of that vocabulary;
`notes/decisions.md`, "Package signatures: raft's first") is listed in `PACKAGES` below.
Its clients are this repository's modules outside the package that import one of its
modules; `etc/api-check.lean` reads the signature and every constant of the package the
clients' declarations use (in their statements and proofs), and classes each use as
`api`, `vocab`, `field`, `instance`, `pure` or `violation` (see its header).

    etc/api-check.py raft              the violations, and a summary of the uses
    etc/api-check.py raft --all        every use, by class
    etc/api-check.py raft --check      exit 1 if there is a violation
    etc/api-check.py raft --json       the raw lines of etc/api-check.lean

Needs an up-to-date `lake build` of the clients (it never builds: it exits, asking for
`lake build`, if `lake build --no-build` finds them out of date).
"""

import argparse
import collections
import json
import os
import re
import subprocess
import sys

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
IMPORT = re.compile(r"^\s*(?:public\s+)?(?:meta\s+)?import\s+(\S+)", re.M)
LOCAL_DIRS = ("Spec", "Proof", "EtcdDeps")

PACKAGES = {
    "raft": {
        "sig": "Perennial.EtcdGrove.raftSig",
        "own": [
            "Spec.go_etcd_io.raft.v3", "Proof.go_etcd_io.raft.v3",
            # raft's specs of the standard-library functions it calls, stated in raft's
            # vocabulary (`ownBigInt`, `confStateDeepEq`) and used by raft alone
            "Spec.math.big", "Proof.math.big", "Spec.crypto.rand", "Proof.crypto.rand",
            "Spec.reflect.DeepEqual", "Proof.reflect.DeepEqual",
        ],
    },
}


def modules():
    """Every module of this repository's specs and proofs, with its imports."""
    out = {}
    for d in LOCAL_DIRS:
        for dp, _, fs in os.walk(os.path.join(ROOT, d)):
            for f in fs:
                if f.endswith(".lean"):
                    p = os.path.join(dp, f)
                    m = os.path.relpath(p, ROOT)[:-5].replace(os.sep, ".")
                    with open(p) as fh:
                        out[m] = IMPORT.findall(fh.read())
    return out


def owned(m, own):
    return any(m == p or m.startswith(p + ".") for p in own)


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("package", choices=sorted(PACKAGES))
    ap.add_argument("--all", action="store_true", help="every use, by class")
    ap.add_argument("--check", action="store_true", help="exit 1 if there is a violation")
    ap.add_argument("--json", action="store_true", help="the raw lines")
    a = ap.parse_args()
    pkg = PACKAGES[a.package]
    mods = modules()
    clients = sorted(m for m, ims in mods.items()
                     if not owned(m, pkg["own"]) and any(owned(i, pkg["own"]) for i in ims))
    if not clients:
        print(f"api-check: {a.package} has no clients")
        return 0
    r = subprocess.run(["lake", "build", "--no-build", *clients], cwd=ROOT,
                       stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    if r.returncode != 0:
        print("api-check: the clients' build is out of date; run `lake build " +
              " ".join(clients) + "` first", file=sys.stderr)
        return 2
    cmd = ["lake", "env", "lean", "--run", "etc/api-check.lean", f"--sig={pkg['sig']}",
           *[f"--own={p}" for p in pkg["own"]], *clients]
    r = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True)
    if r.returncode != 0:
        sys.stderr.write(r.stderr or r.stdout)
        return 2
    if a.json:
        sys.stdout.write(r.stdout)
    rows = [json.loads(l) for l in r.stdout.splitlines() if l.strip()]
    by = collections.defaultdict(list)
    for row in rows:
        by[row["class"]].append(row)
    if not a.json:
        print(f"{a.package}: {len(clients)} client modules, {len(rows)} constants of the "
              f"package used: " + ", ".join(f"{len(by[c])} {c}" for c in sorted(by)))
        classes = sorted(by) if a.all else ["violation"]
        for c in classes:
            for row in sorted(by[c], key=lambda x: (x["module"], x["name"])):
                users = sorted({cm for _, cm in row["clients"]})
                print(f"  {c:9} {row['kind']:9} {row['name']}  ({row['module']})")
                if c == "violation":
                    for u in users:
                        print(f"              used in {u}")
    return 1 if a.check and by["violation"] else 0


if __name__ == "__main__":
    sys.exit(main())
