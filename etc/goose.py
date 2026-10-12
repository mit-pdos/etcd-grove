#!/usr/bin/env python3
"""Regenerate, or check, the Goose translations of etcd-raft and etcd (in `Code/`, `GeneratedProof/`).

usage: etc/goose.py [--check] [--project NAME]... [--src NAME=DIR]... [--perennial DIR]

  --check      translate into a scratch directory and compare with the checked-in
               files; exit 1 (printing a diff) if they differ.  A gate for CI: the
               checked-in translation must be exactly what the pinned translator
               produces from the pinned Go source.
  --project    only this project (etcd-raft, etcd or register; repeatable; default: all).
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
`Perennial.*`, Perennial's).  A project's `parts` translate more of its packages into a
module root of their own (`<root>/Code/`, configured by `<root>/Code/**.toml`): etcd's raft
dependency, in `EtcdDeps/`, whose Go path is that of the etcd-raft project.
Without --check, the generated `.lean` files under `{Code,GeneratedProof}/`
(in the subdirectories the project owns) are replaced by fresh output.  The Goose
configuration (`*.toml`, next to the code) is input and is never touched.

The translator (`goose`, `proofgen`) is built with `go` from Perennial's `goose/`.
The pinned Perennial is `.lake/packages/perennial` when Lake has already checked it
out at the pinned revision, otherwise a clone in `.lake/goose/perennial`.  A
project's source is cloned into `.lake/goose/<name>` at its pinned revision, except
for a project in this repository (`local`), whose source is that directory.
"""

import argparse
import difflib
import json
import os
import shutil
import subprocess
import sys
import tempfile
from dataclasses import dataclass, field

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
WORK = os.path.join(ROOT, ".lake", "goose")


@dataclass
class Part:
    """A translation of some of a project's packages into the module root `root`: for a Go
    path that is also translated from another source (etcd's own raft dependency, whose
    path is etcd-raft's), so that the two have different modules."""
    root: str
    lean_roots: list
    packages: list
    owned: list


@dataclass
class Project:
    name: str
    # The Go source, at a pinned revision (upstream, or a fork that makes the code
    # translatable).  Change the revision here and rerun etc/goose.py.
    repo: str
    rev: str
    # goose's -lean-root PKG=ROOT arguments: Go path prefixes -> Lean module root.
    lean_roots: list
    # Go packages to translate (resolved in the checkout's root module/workspace).
    packages: list
    # Output paths owned by this project, relative to Code/ and GeneratedProof/: a
    # directory, and the `.lean` file of the same name beside it (`go_etcd_io/bbolt`:
    # `bbolt.lean` and `bbolt/`).
    owned: list
    # More translations of packages of the same checkout, each into a module root of
    # its own (`<root>/Code/`, `<root>/GeneratedProof/`, configured by `<root>/Code/**.toml`).
    parts: list = field(default_factory=list)
    # The Go modules of the checkout whose code etc/verified-code.py counts (not its
    # tests or tools); None: every module of the checkout.
    counted_modules: list = None
    # The Go source is this directory of this repository (relative to its root) instead
    # of a fork (`repo`, `rev`: None).
    local: str = None

    @property
    def env(self):
        return self.name.upper().replace("-", "_") + "_SRC"


PROJECTS = [
    Project(
        name="etcd-raft",
        # Upstream, unmodified: the last commit before raftpb moved to protobuf-go v2
        # (2026-04-15; from the next commit on, messages are pointers with getters, see
        # notes/STATUS.md, "Retargeting raft to upstream").
        repo="https://github.com/etcd-io/raft",
        rev="40f8be730b181c22b430ad83845ce477ca76ad15",
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
        counted_modules=["go.etcd.io/raft/v3"],
    ),
    Project(
        name="etcd",
        # Branch `goose-lean`: upstream main (2026-10), the commits that make it
        # translatable, and the one bug fix of `cache-ready-after-retry` (64313a1f8); its
        # two other commits are reverted (no code change unless it fixes a bug). Branch
        # `goose` (upstream main of 2026-03) stays as it is: the Rocq translations
        # (etcd-grove `main`, Perennial `master`) are regenerated from it by name.
        repo="https://github.com/upamanyus/etcd",
        rev="bc8b52a503191e8af023b209a1cc5b54e1025d6d",
        # go.etcd.io/raft/v3 is etcd's own raft dependency (etcd's go.mod), not the raft
        # above: its modules are EtcdDeps.Code.go_etcd_io.raft.v3* (the part below).
        lean_roots=["go.etcd.io/etcd=", "k8s.io=", "google.golang.org=", "go.uber.org=",
                    "go.etcd.io/bbolt=", "go.opentelemetry.io=",
                    "github.com/dustin/go-humanize=", "github.com/prometheus/client_golang=", "net/http=",
                    "github.com/Masterminds/semver=", "go.etcd.io/raft/v3=EtcdDeps"],
        packages=[
            # with bodies (cache/v3.toml)
            "go.etcd.io/etcd/cache/v3",
            # with bodies (client/v3/concurrency.toml): Session, Mutex, Election, STM
            "go.etcd.io/etcd/client/v3/concurrency",
            # with bodies (client/v3/leasing.toml): the leasing KV and its lease cache
            "go.etcd.io/etcd/client/v3/leasing",
            # with bodies (client/v3/experimental/recipes.toml): barrier, double barrier, queue,
            # priority queue, RWMutex
            "go.etcd.io/etcd/client/v3/experimental/recipes",
            # the server's consistent index, with bodies (cindex.toml), or some of them
            # (etcdserver.toml: the apply thread; storage/schema.toml: cindex.go)
            "go.etcd.io/etcd/server/v3/etcdserver/cindex",
            "go.etcd.io/etcd/server/v3/etcdserver",
            "go.etcd.io/etcd/server/v3/storage/schema",
            # with bodies (etcdserver/txn.toml): the server's Range, Put, DeleteRange, Txn over
            # the mvcc core
            "go.etcd.io/etcd/server/v3/etcdserver/txn",
            # with bodies (etcdserver/apply.toml): the applier chain, between the apply thread
            # and the txn package (metrics.go names only)
            "go.etcd.io/etcd/server/v3/etcdserver/apply",
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
            # names only: what the apply package names (api.UpdateCapability,
            # version.DowngradeInfo, the membership requests, semver)
            "go.etcd.io/etcd/server/v3/etcdserver/api",
            "go.etcd.io/etcd/server/v3/etcdserver/version",
            "go.etcd.io/etcd/api/v3/membershippb",
            "go.etcd.io/etcd/api/v3/authpb",
            "github.com/Masterminds/semver/v3",
            "go.etcd.io/etcd/server/v3/etcdserver/errors",
            "go.etcd.io/etcd/server/v3/etcdserver/read",
            "go.etcd.io/etcd/server/v3/lease",
            "go.etcd.io/etcd/server/v3/auth",
            "go.etcd.io/etcd/pkg/v3/contention",
            "go.etcd.io/etcd/pkg/v3/idutil",
            "go.etcd.io/etcd/pkg/v3/notify",
            "go.etcd.io/etcd/pkg/v3/pbutil",
            "go.etcd.io/etcd/pkg/v3/traceutil",
            # names only: the type of mvcc's store.fifoSched
            "go.etcd.io/etcd/pkg/v3/schedule",
            "go.etcd.io/etcd/pkg/v3/wait",
            "go.etcd.io/etcd/client/pkg/v3/types",
            "go.etcd.io/etcd/client/pkg/v3/verify",
            "go.etcd.io/etcd/client/pkg/v3/transport",
            "go.etcd.io/etcd/pkg/v3/featuregate",
            "go.etcd.io/etcd/server/v3/etcdserver/api/v3discovery",
            "go.etcd.io/bbolt",
            # bbolt's page-id helpers, with bodies (bbolt/internal/common.toml)
            "go.etcd.io/bbolt/internal/common",
            "go.opentelemetry.io/contrib/instrumentation/google.golang.org/grpc/otelgrpc",
            "google.golang.org/protobuf/proto",
            "google.golang.org/protobuf/reflect/protoreflect",
            "go.uber.org/zap",
            "go.uber.org/zap/zapcore",
            "github.com/dustin/go-humanize",
            # names only: the metrics mvcc's transactions and key index update
            "github.com/prometheus/client_golang/prometheus",
            # a standard-library package Perennial does not translate: its names are here
            "net/http",
            # types and names only (their .toml)
            "go.etcd.io/etcd/client/v3",
            "go.etcd.io/etcd/api/v3/etcdserverpb",
            "go.etcd.io/etcd/api/v3/mvccpb",
            "go.etcd.io/etcd/api/v3/v3rpc/rpctypes",
            "k8s.io/utils/third_party/forked/golang/btree",
            # names only: what `clientv3.WatchResponse.Err` calls
            "google.golang.org/grpc/codes",
            "google.golang.org/grpc/status",
            # names only: the target of the alias grpc/status.Status (client/v3/leasing)
            "google.golang.org/grpc/internal/status",
            # the types of protobuf messages' fields (protoimpl.MessageState, ...)
            "google.golang.org/protobuf/runtime/protoimpl",
            "google.golang.org/protobuf/internal/impl",
            "google.golang.org/protobuf/internal/pragma",
            # names only: the types of clientv3.Client's fields
            "google.golang.org/grpc",
            "google.golang.org/grpc/credentials",
            "go.etcd.io/etcd/client/v3/credentials",
            "go.etcd.io/etcd/client/v3/internal/resolver",
            # (and go.uber.org/zap, above)
        ],
        owned=[os.path.join("go_etcd_io", "etcd"), os.path.join("go_etcd_io", "bbolt"),
               os.path.join("github_com", "prometheus"),
               os.path.join("github_com", "Masterminds"),
               "k8s_io", "google_golang_org", "go_uber_org", "go_opentelemetry_io",
               os.path.join("net", "http"), os.path.join("github_com", "dustin")],
        parts=[
            # etcd's own raft dependency (go.etcd.io/raft/v3 in etcd's go.mod), whose
            # raftpb is protobuf-go v2: not the gogoproto etcd-raft above, but the same
            # Go path, so into a root of its own (modules EtcdDeps.Code.go_etcd_io.raft.v3*;
            # both define `Perennial.go_etcd_io.raft.v3.*`, so no module imports both).
            Part(
                root="EtcdDeps",
                lean_roots=["go.etcd.io/raft/v3=EtcdDeps", "google.golang.org="],
                packages=["go.etcd.io/raft/v3", "go.etcd.io/raft/v3/raftpb"],
                owned=[os.path.join("go_etcd_io", "raft")],
            ),
        ],
        # etcd itself: not its tests, tools or root module
        counted_modules=[
            "go.etcd.io/etcd/api/v3",
            "go.etcd.io/etcd/cache/v3",
            "go.etcd.io/etcd/client/pkg/v3",
            "go.etcd.io/etcd/client/v3",
            "go.etcd.io/etcd/etcdctl/v3",
            "go.etcd.io/etcd/etcdutl/v3",
            "go.etcd.io/etcd/pkg/v3",
            "go.etcd.io/etcd/server/v3",
        ],
    ),
    Project(
        name="register",
        # An example application on raft's Node: a replicated string register. A Go
        # module of this repository, whose go.mod requires go.etcd.io/raft/v3 at the
        # revision pinned above (keep the two in step).
        repo=None,
        rev=None,
        local=os.path.join("examples", "register"),
        lean_roots=["github.com/mit-pdos/etcd-grove=", "go.etcd.io/raft/v3="],
        packages=["."],
        owned=[os.path.join("github_com", "mit_pdos", "etcd_grove")],
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


def lean_files(d, owned):
    """The `.lean` files under `d/{Code,GeneratedProof}/` at the paths `owned`."""
    out = {}
    for sub in ("Code", "GeneratedProof"):
        for o in owned:
            base = os.path.join(d, sub, o)
            paths = [base + ".lean"] if os.path.isfile(base + ".lean") else []
            for dp, _, fs in os.walk(base):
                paths.extend(os.path.join(dp, f) for f in fs if f.endswith(".lean"))
            for path in paths:
                out[os.path.relpath(path, d)] = open(path, encoding="utf-8").read()
    return out


def pieces(proj):
    """The translations of `proj`: (module root, -lean-root arguments, packages, owned)."""
    return [("", proj.lean_roots, proj.packages, proj.owned)] + [
        (p.root, p.lean_roots, p.packages, p.owned) for p in proj.parts]


def source(proj, local, check):
    """The checkout to translate, and a description of it for the output."""
    if proj.local is not None:
        if local is not None:
            sys.exit(f"goose.py: {proj.name} is translated from {proj.local}; no --src")
        return os.path.join(ROOT, proj.local), proj.local
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
    out = tempfile.mkdtemp(prefix="goose-", dir=WORK)
    try:
        # path relative to ROOT -> (new content or None, old content or None)
        new, old = {}, {}
        for i, (root, lean_roots, packages, owned) in enumerate(pieces(proj)):
            lib_dir = os.path.join(ROOT, root)
            piece_out = os.path.join(out, str(i))
            config = os.path.join(lib_dir, "Code")
            roots = [a for r in lean_roots for a in ("-lean-root", r)]
            for tool, sub in (("goose", "Code"), ("proofgen", "GeneratedProof")):
                run([os.path.join(bindir, tool)] + roots +
                    ["-out", os.path.join(piece_out, sub), "-configdir", config, "-dir", src]
                    + packages)
            for f, c in lean_files(piece_out, owned).items():
                new[os.path.join(root, f)] = (c, os.path.join(piece_out, f))
            for f, c in lean_files(lib_dir, owned).items():
                old[os.path.join(root, f)] = c
        newc = {f: c for f, (c, _) in new.items()}
        changed = sorted(f for f in newc.keys() | old.keys() if newc.get(f) != old.get(f))
        if check:
            if not changed:
                print(f"goose.py: the translation of {proj.name} is up to date (Perennial "
                      f"{perennial_rev}, {proj.name} {desc})")
                return True
            for f in changed:
                sys.stdout.writelines(difflib.unified_diff(
                    old.get(f, "").splitlines(keepends=True), newc.get(f, "").splitlines(keepends=True),
                    "checked-in/" + f, "translator/" + f))
            print(f"goose.py: {len(changed)} file(s) of the translation of {proj.name} differ from what Perennial "
                  f"{perennial_rev} produces from {proj.name} {desc}; run etc/goose.py",
                  file=sys.stderr)
            return False
        for f in changed:
            dst = os.path.join(ROOT, f)
            if f in new:
                os.makedirs(os.path.dirname(dst), exist_ok=True)
                shutil.copyfile(new[f][1], dst)
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
