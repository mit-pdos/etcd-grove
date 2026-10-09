#!/usr/bin/env python3
"""Regenerate, or check, the Goose translations of etcd-raft (`EtcdRaft/`) and etcd (`EtcdCache/`).

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

Each project is a Go repository at a pinned revision, translated into one Lake
library (a directory of this repository): the packages in its list, with goose's
`-lean-root` mapping every non-standard-library Go path the translation reaches to
that library (standard-library packages stay `Perennial.*`, Perennial's).
Without --check, the generated `.lean` files under `<lib>/{Code,GeneratedProof}/`
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
    # The Lake library (and directory) the translation goes to.
    lib: str
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
        # Modules EtcdRaft.Code.*, EtcdRaft.GeneratedProof.*: the library EtcdRaft.
        lean_roots=["go.etcd.io/raft/v3=EtcdRaft"],
        lib="EtcdRaft",
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
        lib="EtcdCache",
        # go.etcd.io/raft/v3 is etcd's own raft dependency (v3.7.0 in etcd's go.mod), whose
        # raftpb is protobuf-go v2: not the gogoproto fork EtcdRaft/ translates, so it is
        # translated here too (both define `Perennial.go_etcd_io.raft.v3.*`, so no module
        # may import both). net/http is a standard-library package Perennial does not
        # translate, so its names are here.
        lean_roots=["go.etcd.io/etcd=EtcdCache", "k8s.io=EtcdCache",
                    "google.golang.org=EtcdCache", "go.uber.org=EtcdCache",
                    "go.etcd.io/bbolt=EtcdCache", "go.opentelemetry.io=EtcdCache",
                    "github.com/dustin/go-humanize=EtcdCache",
                    "net/http=EtcdCache", "go.etcd.io/raft/v3=EtcdCache"],
        packages=[
            # with bodies (cache/v3.toml)
            "go.etcd.io/etcd/cache/v3",
            # the server's consistent index, with bodies (cindex.toml), or some of them
            # (etcdserver.toml: the apply thread; storage/schema.toml: cindex.go)
            "go.etcd.io/etcd/server/v3/etcdserver/cindex",
            "go.etcd.io/etcd/server/v3/etcdserver",
            "go.etcd.io/etcd/server/v3/storage/schema",
            # types and names only: what the server's types and the apply thread name
            "go.etcd.io/etcd/server/v3/storage",
            "go.etcd.io/etcd/server/v3/storage/backend",
            "go.etcd.io/etcd/server/v3/storage/mvcc",
            "go.etcd.io/etcd/server/v3/config",
            "go.etcd.io/etcd/server/v3/etcdserver/api/membership",
            "go.etcd.io/etcd/server/v3/etcdserver/api/rafthttp",
            "go.etcd.io/etcd/server/v3/etcdserver/api/snap",
            "go.etcd.io/etcd/server/v3/etcdserver/api/v2stats",
            "go.etcd.io/etcd/server/v3/etcdserver/api/v3alarm",
            "go.etcd.io/etcd/server/v3/etcdserver/api/v3compactor",
            "go.etcd.io/etcd/server/v3/etcdserver/apply",
            "go.etcd.io/etcd/server/v3/etcdserver/errors",
            "go.etcd.io/etcd/server/v3/etcdserver/read",
            "go.etcd.io/etcd/server/v3/lease",
            "go.etcd.io/etcd/server/v3/auth",
            "go.etcd.io/etcd/pkg/v3/contention",
            "go.etcd.io/etcd/pkg/v3/idutil",
            "go.etcd.io/etcd/pkg/v3/notify",
            "go.etcd.io/etcd/pkg/v3/pbutil",
            "go.etcd.io/etcd/pkg/v3/traceutil",
            "go.etcd.io/etcd/pkg/v3/wait",
            "go.etcd.io/etcd/client/pkg/v3/types",
            "go.etcd.io/etcd/client/pkg/v3/verify",
            "go.etcd.io/etcd/client/pkg/v3/transport",
            "go.etcd.io/etcd/pkg/v3/featuregate",
            "go.etcd.io/etcd/server/v3/etcdserver/api/v3discovery",
            "go.etcd.io/bbolt",
            "go.opentelemetry.io/contrib/instrumentation/google.golang.org/grpc/otelgrpc",
            "google.golang.org/protobuf/proto",
            "google.golang.org/protobuf/reflect/protoreflect",
            "go.etcd.io/raft/v3",
            "go.etcd.io/raft/v3/raftpb",
            "go.uber.org/zap",
            "go.uber.org/zap/zapcore",
            "github.com/dustin/go-humanize",
            "net/http",
            # types and names only (their .toml)
            "go.etcd.io/etcd/client/v3",
            "go.etcd.io/etcd/api/v3/etcdserverpb",
            "go.etcd.io/etcd/api/v3/mvccpb",
            "go.etcd.io/etcd/api/v3/v3rpc/rpctypes",
            "k8s.io/utils/third_party/forked/golang/btree",
            # the types of protobuf messages' fields (protoimpl.MessageState, ...)
            "google.golang.org/protobuf/runtime/protoimpl",
            "google.golang.org/protobuf/internal/impl",
        ],
        # (all of go_etcd_io/ here: EtcdRaft's go_etcd_io/raft is in EtcdRaft/)
        owned=["go_etcd_io", "k8s_io", "google_golang_org", "go_uber_org",
               "go_opentelemetry_io", "net",
               os.path.join("github_com", "dustin")],
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
    lib_dir = os.path.join(ROOT, proj.lib)
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
                print(f"goose.py: the translation in {proj.lib}/ is up to date (Perennial "
                      f"{perennial_rev}, {proj.name} {desc})")
                return True
            for f in changed:
                sys.stdout.writelines(difflib.unified_diff(
                    old.get(f, "").splitlines(keepends=True), new.get(f, "").splitlines(keepends=True),
                    "checked-in/" + f, "translator/" + f))
            print(f"goose.py: {len(changed)} file(s) of {proj.lib}/ differ from what Perennial "
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
        print(f"goose.py: {proj.lib}/: {len(changed)} file(s) updated (Perennial {perennial_rev}, "
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
