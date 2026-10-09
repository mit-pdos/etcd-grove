#!/usr/bin/env python3
"""Regenerate, or check, the Goose translations of etcd-raft and etcd (in `Code/`, `GeneratedProof/`).

usage: etc/goose.py [--check] [--project NAME]... [--src NAME=DIR]... [--perennial DIR]

  --check      translate into a scratch directory and compare with the checked-in
               files; exit 1 (printing a diff) if they differ.  A gate for CI: the
               checked-in translation must be exactly what the pinned translator
               produces from the pinned Go source.
  --project    only this project (etcd-raft or etcd; repeatable; default: all).
  --src        translate project NAME from the local checkout DIR instead of
               cloning its pinned revision (default: $<NAME>_SRC, e.g. $ETCD_SRC,
               $ETCD_RAFT_SRC).  For a pinned revision not yet pushed, or for trying
               a source change.  The output says so; with --check, DIR must be at
               the pinned revision with no uncommitted changes.
  --perennial  use the translator of this Perennial checkout instead of the pinned
               one (default: $PERENNIAL_DIR, else the revision pinned in
               lake-manifest.json); for trying a translator change locally.

Each project is a Go repository at a pinned revision, translated into `Code/` and
`GeneratedProof/`: the packages in its list, with goose's `-lean-root PKG=` mapping
every non-standard-library Go path the translation reaches to the empty root
(modules `Code.<pkg>`, `GeneratedProof.<pkg>`; standard-library packages stay
`Perennial.*`, Perennial's).
Without --check, the generated `.lean` files under `{Code,GeneratedProof}/`
(in the subdirectories the project owns) are replaced by fresh output.  The Goose
configuration (`*.toml`, next to the code) is input and is never touched.

The translator (`goose`, `proofgen`) is built with `go` from Perennial's `goose/`.
The pinned Perennial is `.lake/packages/perennial` when Lake has already checked it
out at the pinned revision, otherwise a clone in `.lake/goose/perennial`.  A
project's source is cloned into `.lake/goose/<name>` at its pinned revision.
"""

import argparse
import difflib
import json
import os
import shutil
import subprocess
import sys
import tempfile
from dataclasses import dataclass

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
WORK = os.path.join(ROOT, ".lake", "goose")


@dataclass
class Project:
    name: str
    # The Go source: a fork that makes the code translatable.  Change the revision
    # here and rerun etc/goose.py.
    repo: str
    rev: str
    # goose's -lean-root PKG=ROOT arguments: Go path prefixes -> Lean module root.
    lean_roots: list
    # Go packages to translate (resolved in the checkout's root module/workspace).
    packages: list
    # Output subdirectories owned by this project, relative to Code/ and GeneratedProof/.
    owned: list

    @property
    def env(self):
        return self.name.upper().replace("-", "_") + "_SRC"


PROJECTS = [
    Project(
        name="etcd-raft",
        repo="https://github.com/upamanyus/etcd-raft",
        rev="531b20c6251eb54f79ed1ca242430a20aaaae0c3",
        # Modules Code.go_etcd_io.raft.v3*, GeneratedProof.go_etcd_io.raft.v3*.
        lean_roots=["go.etcd.io/raft/v3="],
        packages=[
            ".",
            "go.etcd.io/raft/v3/confchange",
            "go.etcd.io/raft/v3/quorum",
            "go.etcd.io/raft/v3/raftpb",
            "go.etcd.io/raft/v3/tracker",
        ],
        owned=[os.path.join("go_etcd_io", "raft")],
    ),
    Project(
        name="etcd",
        # Branch `goose-lean`: upstream main (2026-10) plus the commits that make it
        # translatable. Branch `goose` (upstream main of 2026-03) stays as it is: the
        # Rocq translations (etcd-grove `main`, Perennial `master`) are regenerated
        # from it by name.
        repo="https://github.com/upamanyus/etcd",
        rev="48fd5a5071608e5c075b588c50e4efbfe300b00a",
        lean_roots=["go.etcd.io/etcd=", "k8s.io=", "google.golang.org="],
        packages=[
            # with bodies (cache/v3.toml)
            "go.etcd.io/etcd/cache/v3",
            # types and names only (their .toml)
            "go.etcd.io/etcd/client/v3",
            "go.etcd.io/etcd/api/v3/etcdserverpb",
            "go.etcd.io/etcd/api/v3/mvccpb",
            "go.etcd.io/etcd/api/v3/v3rpc/rpctypes",
            "k8s.io/utils/third_party/forked/golang/btree",
            # the types of protobuf messages' fields (protoimpl.MessageState, ...)
            "google.golang.org/protobuf/runtime/protoimpl",
            "google.golang.org/protobuf/internal/impl",
            "google.golang.org/protobuf/internal/pragma",
        ],
        owned=[os.path.join("go_etcd_io", "etcd"), "k8s_io", "google_golang_org"],
    ),
]


def run(args, cwd=None, quiet=False):
    if not quiet:
        print("+ " + " ".join(args), file=sys.stderr)
    subprocess.run(args, cwd=cwd, check=True)


def git_head(d):
    r = subprocess.run(["git", "-C", d, "rev-parse", "HEAD"], capture_output=True, text=True)
    return r.stdout.strip() if r.returncode == 0 else None


def git_dirty(d):
    r = subprocess.run(["git", "-C", d, "status", "--porcelain", "--untracked-files=no"],
                       capture_output=True, text=True, check=True)
    return r.stdout.strip() != ""


def checkout(url, rev, d):
    """A checkout of `url` at `rev` in `d` (cloned or fetched as needed)."""
    if git_head(d) == rev:
        return d
    if not os.path.isdir(os.path.join(d, ".git")):
        os.makedirs(d, exist_ok=True)
        run(["git", "init", "-q", d])
        run(["git", "-C", d, "remote", "add", "origin", url])
    try:
        run(["git", "-C", d, "fetch", "-q", "--depth", "1", "origin", rev])
    except subprocess.CalledProcessError:
        sys.exit(f"goose.py: cannot fetch {rev} from {url}; if it is not pushed yet, "
                 f"name a local checkout with --src or ${{NAME}}_SRC")
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


def lean_files(d, proj):
    out = {}
    for sub in ("Code", "GeneratedProof"):
        for owned in proj.owned:
            base = os.path.join(d, sub, owned)
            for dp, _, fs in os.walk(base):
                for f in fs:
                    if f.endswith(".lean"):
                        rel = os.path.relpath(os.path.join(dp, f), d)
                        out[rel] = open(os.path.join(dp, f), encoding="utf-8").read()
    return out


def source(proj, local, check):
    """The checkout to translate, and a description of it for the output."""
    if local is None:
        return checkout(proj.repo, proj.rev, os.path.join(WORK, proj.name)), proj.rev[:12]
    local = os.path.abspath(local)
    head, dirty = git_head(local), git_dirty(local)
    print(f"goose.py: {proj.name}: USING THE LOCAL CHECKOUT {local} (HEAD {head}"
          f"{', with uncommitted changes' if dirty else ''}) instead of cloning "
          f"{proj.repo} at {proj.rev}", file=sys.stderr)
    if head != proj.rev or dirty:
        msg = (f"goose.py: {proj.name}: the local checkout is not the pinned revision "
               f"{proj.rev}" + (" (uncommitted changes)" if dirty else ""))
        if check:
            sys.exit(msg + "; --check needs the pinned revision")
        print(msg + "; the output is not what the pin produces", file=sys.stderr)
    return local, f"{proj.rev[:12]} (local checkout {local})"


def translate(proj, src, bindir, perennial_rev, desc, check):
    """Translate `proj`; return True if the checked-in translation is (now) up to date."""
    lib_dir = ROOT
    out = tempfile.mkdtemp(prefix="goose-", dir=WORK)
    try:
        config = os.path.join(lib_dir, "Code")
        roots = [a for r in proj.lean_roots for a in ("-lean-root", r)]
        for tool, sub in (("goose", "Code"), ("proofgen", "GeneratedProof")):
            run([os.path.join(bindir, tool), "-lean"] + roots +
                ["-out", os.path.join(out, sub), "-configdir", config, "-dir", src]
                + proj.packages)
        new, old = lean_files(out, proj), lean_files(lib_dir, proj)
        changed = sorted(f for f in new.keys() | old.keys() if new.get(f) != old.get(f))
        if check:
            if not changed:
                print(f"goose.py: the translation of {proj.name} is up to date (Perennial "
                      f"{perennial_rev}, {proj.name} {desc})")
                return True
            for f in changed:
                sys.stdout.writelines(difflib.unified_diff(
                    old.get(f, "").splitlines(keepends=True), new.get(f, "").splitlines(keepends=True),
                    "checked-in/" + f, "translator/" + f))
            print(f"goose.py: {len(changed)} file(s) of the translation of {proj.name} differ from what Perennial "
                  f"{perennial_rev} produces from {proj.name} {desc}; run etc/goose.py",
                  file=sys.stderr)
            return False
        for f in changed:
            dst = os.path.join(lib_dir, f)
            if f in new:
                os.makedirs(os.path.dirname(dst), exist_ok=True)
                shutil.copyfile(os.path.join(out, f), dst)
            else:
                os.remove(dst)
        print(f"goose.py: {proj.name}: {len(changed)} file(s) updated (Perennial {perennial_rev}, "
              f"{proj.name} {desc})")
        return True
    finally:
        shutil.rmtree(out, ignore_errors=True)


def main():
    names = [p.name for p in PROJECTS]
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--project", action="append", choices=names)
    ap.add_argument("--src", action="append", default=[], metavar="NAME=DIR")
    ap.add_argument("--perennial", default=os.environ.get("PERENNIAL_DIR"))
    args = ap.parse_args()

    projects = [p for p in PROJECTS if not args.project or p.name in args.project]
    local = {p.name: os.environ[p.env] for p in PROJECTS if os.environ.get(p.env)}
    for s in args.src:
        name, sep, d = s.partition("=")
        if not sep or name not in names:
            ap.error(f"--src {s}: expected NAME=DIR with NAME one of {', '.join(names)}")
        local[name] = d

    if args.perennial:
        perennial, rev = os.path.abspath(args.perennial), git_head(args.perennial) or "?"
        rev += " (--perennial " + perennial + ")"
    else:
        perennial, rev = pinned_perennial()
    sources = [(p,) + source(p, local.get(p.name), args.check) for p in projects]

    bindir = os.path.join(WORK, "bin")
    os.makedirs(bindir, exist_ok=True)
    run(["go", "build", "-o", bindir + os.sep, "./goose/cmd/goose", "./goose/cmd/proofgen"],
        cwd=perennial)

    ok = [translate(p, src, bindir, rev, desc, args.check) for p, src, desc in sources]
    if not all(ok):
        sys.exit(1)


if __name__ == "__main__":
    main()
