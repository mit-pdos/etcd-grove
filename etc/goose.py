#!/usr/bin/env python3
"""Regenerate, or check, the Goose translation of etcd-raft in `EtcdRaft/`.

usage: etc/goose.py [--check] [--perennial DIR]

  --check      translate into a scratch directory and compare with the checked-in
               files; exit 1 (printing a diff) if they differ.  A gate for CI: the
               checked-in translation must be exactly what the pinned translator
               produces from the pinned etcd-raft source.
  --perennial  use the translator of this Perennial checkout instead of the pinned
               one (default: $PERENNIAL_DIR, else the revision pinned in
               lake-manifest.json); for trying a translator change locally.

Without --check, the generated `.lean` files under `EtcdRaft/{Code,GeneratedProof}/
go_etcd_io/` are replaced by fresh output.  The Goose configuration
(`*.toml`, next to the code) is input and is never touched.

The translator (`goose`, `proofgen`) is built with `go` from Perennial's `goose/`.
The pinned Perennial is `.lake/packages/perennial` when Lake has already checked it
out at the pinned revision, otherwise a clone in `.lake/goose/perennial`.  etcd-raft
is cloned into `.lake/goose/etcd-raft` at `ETCD_RAFT_REV`.
"""

import argparse
import difflib
import json
import os
import shutil
import subprocess
import sys
import tempfile

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
WORK = os.path.join(ROOT, ".lake", "goose")
GOOSE_DIR = os.path.join(ROOT, "EtcdRaft")

# The etcd-raft source that is translated: the `goose` branch of the fork, which
# makes etcd-raft translatable.  Change the revision here and rerun etc/goose.py.
ETCD_RAFT_REPO = "https://github.com/upamanyus/etcd-raft"
ETCD_RAFT_REV = "531b20c6251eb54f79ed1ca242430a20aaaae0c3"
# The Lean module root of the translation (goose's -lean-root): its modules are
# EtcdRaft.Code.*, EtcdRaft.GeneratedProof.*, the library EtcdRaft of lakefile.toml.
LEAN_ROOT = "go.etcd.io/raft/v3=EtcdRaft"
PACKAGES = [
    ".",
    "go.etcd.io/raft/v3/confchange",
    "go.etcd.io/raft/v3/quorum",
    "go.etcd.io/raft/v3/raftpb",
    "go.etcd.io/raft/v3/tracker",
]
# Output subdirectories owned by this script, relative to Code/ and GeneratedProof/.
OWNED = os.path.join("go_etcd_io", "raft")


def run(args, cwd=None, quiet=False):
    if not quiet:
        print("+ " + " ".join(args), file=sys.stderr)
    subprocess.run(args, cwd=cwd, check=True)


def git_head(d):
    r = subprocess.run(["git", "-C", d, "rev-parse", "HEAD"], capture_output=True, text=True)
    return r.stdout.strip() if r.returncode == 0 else None


def checkout(url, rev, d):
    """A checkout of `url` at `rev` in `d` (cloned or fetched as needed)."""
    if git_head(d) == rev:
        return d
    if not os.path.isdir(os.path.join(d, ".git")):
        os.makedirs(d, exist_ok=True)
        run(["git", "init", "-q", d])
        run(["git", "-C", d, "remote", "add", "origin", url])
    run(["git", "-C", d, "fetch", "-q", "--depth", "1", "origin", rev])
    run(["git", "-C", d, "checkout", "-q", "--detach", "FETCH_HEAD"])
    if git_head(d) != rev:
        sys.exit(f"goose.py: {url} at {rev}: checked out {git_head(d)} instead")
    return d


def pinned_perennial():
    manifest = json.load(open(os.path.join(ROOT, "lake-manifest.json")))
    (p,) = [p for p in manifest["packages"] if p["name"] == "perennial"]
    lake_dir = os.path.join(ROOT, ".lake", "packages", "perennial")
    if git_head(lake_dir) == p["rev"]:
        return lake_dir, p["rev"]
    return checkout(p["url"], p["rev"], os.path.join(WORK, "perennial")), p["rev"]


def lean_files(d):
    out = {}
    for sub in ("Code", "GeneratedProof"):
        base = os.path.join(d, sub, OWNED)
        for dp, _, fs in os.walk(base):
            for f in fs:
                if f.endswith(".lean"):
                    rel = os.path.relpath(os.path.join(dp, f), d)
                    out[rel] = open(os.path.join(dp, f), encoding="utf-8").read()
    return out


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--perennial", default=os.environ.get("PERENNIAL_DIR"))
    args = ap.parse_args()

    if args.perennial:
        perennial, rev = os.path.abspath(args.perennial), git_head(args.perennial) or "?"
        rev += " (--perennial " + perennial + ")"
    else:
        perennial, rev = pinned_perennial()
    raft = checkout(ETCD_RAFT_REPO, ETCD_RAFT_REV, os.path.join(WORK, "etcd-raft"))

    bindir = os.path.join(WORK, "bin")
    os.makedirs(bindir, exist_ok=True)
    run(["go", "build", "-o", bindir + os.sep, "./goose/cmd/goose", "./goose/cmd/proofgen"],
        cwd=perennial)

    out = tempfile.mkdtemp(prefix="goose-", dir=WORK)
    try:
        config = os.path.join(GOOSE_DIR, "Code")
        for tool, sub in (("goose", "Code"), ("proofgen", "GeneratedProof")):
            run([os.path.join(bindir, tool), "-lean", "-lean-root", LEAN_ROOT,
                 "-out", os.path.join(out, sub),
                 "-configdir", config, "-dir", raft] + PACKAGES)
        new, old = lean_files(out), lean_files(GOOSE_DIR)
        changed = sorted(f for f in new.keys() | old.keys() if new.get(f) != old.get(f))
        if args.check:
            if not changed:
                print(f"goose.py: the translation in EtcdRaft/ is up to date (Perennial {rev}, "
                      f"etcd-raft {ETCD_RAFT_REV[:12]})")
                return
            for f in changed:
                sys.stdout.writelines(difflib.unified_diff(
                    old.get(f, "").splitlines(keepends=True), new.get(f, "").splitlines(keepends=True),
                    "checked-in/" + f, "translator/" + f))
            sys.exit(f"goose.py: {len(changed)} file(s) of EtcdRaft/ differ from what Perennial "
                     f"{rev} produces from etcd-raft {ETCD_RAFT_REV[:12]}; run etc/goose.py")
        for f in changed:
            dst = os.path.join(GOOSE_DIR, f)
            if f in new:
                os.makedirs(os.path.dirname(dst), exist_ok=True)
                shutil.copyfile(os.path.join(out, f), dst)
            else:
                os.remove(dst)
        print(f"goose.py: {len(changed)} file(s) updated (Perennial {rev})")
    finally:
        shutil.rmtree(out, ignore_errors=True)


if __name__ == "__main__":
    main()
