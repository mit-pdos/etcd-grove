#!/usr/bin/env python3
"""The k8s etcd3 driver's copy of Kubernetes' checker is upstream's, plus one named patch
(k8s 7g, `notes/k8s-7g-scope.md` §1.1, Q2).

`examples/k8s/etcd3/correctness/` is a copy of the package
`k8s.io/apiserver/pkg/storage/testing/correctness` (the checker `TestCorrectness` runs: `Model`,
`Replay`, `WatchValidator`) at the `k8s.io/apiserver` version the driver's `go.mod` requires, with
`etc/k8s-correctness/d30g.patch` applied (the Model's `NeedsRewrite`, D30g). The closed k8s etcd3
theorems say that this checker accepts the driver's failure-free histories, so the copy is part of
what a reader trusts as the checker's text: this script makes "upstream plus the patch" mechanical.

It takes the files `FILES` from the module (`go mod download -json`, so from the module cache),
applies the patch to a temporary copy, and requires each to be byte for byte the driver's copy. It
also requires the copy's directory to hold no other non-test Go file (a file added beside them
would be checker text that is not upstream's). Test files (`*_test.go`) are the driver's own.

`go.mod` may replace `k8s.io/apiserver` only by the one fork pinned in `FORK` (module path and
version, exactly: `upamanyus/kubernetes` branch `goose-lean-fmt1`, `ef23adaea`, real `fmt` stage 1,
mit-pdos/etcd-grove#9). The copy's provenance stays the required upstream version, and the fork is
checked against it file by file over the whole module: every file is upstream's byte for byte, but the
files of `FORK_PATCHES`, which must be upstream's with that patch applied (`Preconditions.Check`'s UIDs
converted to `string` before `%v`: byte-identical output), and the test files `FORK_ADDED`, which
upstream lacks. Any other difference (a file changed, added or removed) fails.

Needs `go` (with network or the module cache) and `patch`. Prints one line on success; exits 1 on a
difference.
"""
import json, os, pathlib, re, shutil, subprocess, sys, tempfile

ROOT = pathlib.Path(__file__).resolve().parent.parent
MODDIR = ROOT / "examples/k8s/etcd3"
COPY = MODDIR / "correctness"
PATCH = ROOT / "etc/k8s-correctness/d30g.patch"
MODULE = "k8s.io/apiserver"
PKG = "pkg/storage/testing/correctness"
# the package's files the driver copies (storage.go, the Model as a storage.Interface, and
# correctness.go, upstream's table of test steps, are not part of the checker)
FILES = ["types.go", "model.go", "replay.go", "watch.go", "consistency.go"]
# the one replacement of MODULE allowed: (module path, version) of the pinned fork, and how it differs
# from the required upstream version: files patched (path in the module -> patch) and test files added
FORK = ("github.com/upamanyus/kubernetes/staging/src/k8s.io/apiserver",
        "v0.0.0-20261124053658-ef23adaea1b3")
FORK_PATCHES = {"pkg/storage/interfaces.go": ROOT / "etc/k8s-correctness/fork-fmt1.patch"}
FORK_ADDED = ["pkg/storage/interfaces_fmt_test.go"]


def fail(msg):
    print(f"k8s-correctness: FAILED: {msg}")
    sys.exit(1)


def pinned_version():
    """The required version of MODULE, and whether go.mod replaces it (by FORK only)."""
    gomod = (MODDIR / "go.mod").read_text()
    m = re.search(r"^\s*" + re.escape(MODULE) + r"\s+(\S+)", gomod, re.M)
    if not m:
        fail(f"{MODULE} not required in {MODDIR / 'go.mod'}")
    forked = False
    for r in re.finditer(r"^\s*replace\s+" + re.escape(MODULE) + r"\b(.*)$", gomod, re.M):
        if r.group(1).split() != ["=>", FORK[0], FORK[1]] or forked:
            fail(f"{MODULE} is replaced in go.mod by something other than the pinned fork "
                 f"{FORK[0]} {FORK[1]}: {r.group(0).strip()}")
        forked = True
    return m.group(1), forked


def module_dir(module, version):
    """The module's root directory in the module cache."""
    env = dict(os.environ, GOWORK="off", GOFLAGS="-mod=mod")
    out = subprocess.run(["go", "mod", "download", "-json", f"{module}@{version}"], cwd=MODDIR,
                         env=env, capture_output=True, text=True)
    if out.returncode != 0:
        fail(f"go mod download {module}@{version}: {out.stderr.strip() or out.stdout.strip()}")
    d = json.loads(out.stdout).get("Dir")
    if not d:
        fail(f"go mod download {module}@{version}: no Dir")
    return pathlib.Path(d)


def check_fork(up, version):
    """The fork's module is upstream's (`up`, at `version`) but for FORK_PATCHES and FORK_ADDED."""
    fk = module_dir(*FORK)
    fu = {p.relative_to(up).as_posix() for p in up.rglob("*") if p.is_file()}
    ff = {p.relative_to(fk).as_posix() for p in fk.rglob("*") if p.is_file()}
    if sorted(ff - fu) != sorted(FORK_ADDED) or fu - ff:
        fail(f"the fork {FORK[0]}@{FORK[1]} adds {sorted(ff - fu)} (allowed: {FORK_ADDED}) "
             f"and removes {sorted(fu - ff)} relative to {MODULE}@{version}")
    with tempfile.TemporaryDirectory() as tmp:
        for f in sorted(fu):
            want = (up / f).read_bytes()
            if f in FORK_PATCHES:
                t = pathlib.Path(tmp) / pathlib.Path(f).name
                t.write_bytes(want)
                patch = FORK_PATCHES[f]
                r = subprocess.run(["patch", "-s", f"-p{f.count('/') + 1}", "--no-backup-if-mismatch",
                                    "-d", tmp, "-i", str(patch)], capture_output=True, text=True)
                if r.returncode != 0:
                    fail(f"{patch.relative_to(ROOT)} does not apply to {MODULE}@{version}'s {f}: "
                         f"{r.stdout}{r.stderr}")
                want = t.read_bytes()
            if (fk / f).read_bytes() != want:
                how = f"with {FORK_PATCHES[f].relative_to(ROOT)} applied" if f in FORK_PATCHES else ""
                fail(f"the fork {FORK[0]}@{FORK[1]}'s {f} differs from {MODULE}@{version}'s {how}")


def main():
    version, forked = pinned_version()
    up = module_dir(MODULE, version)
    if forked:
        check_fork(up, version)
    src = up / PKG
    extra = sorted(p.name for p in COPY.glob("*.go")
                   if not p.name.endswith("_test.go") and p.name not in FILES)
    if extra:
        fail(f"{COPY.relative_to(ROOT)} holds non-test Go files that are not upstream's: {extra}")
    with tempfile.TemporaryDirectory() as tmp:
        for f in FILES:
            if not (src / f).exists():
                fail(f"{MODULE}@{version} has no {PKG}/{f}")
            shutil.copyfile(src / f, pathlib.Path(tmp) / f)
        r = subprocess.run(["patch", "-s", "-p5", "--no-backup-if-mismatch", "-d", tmp, "-i", str(PATCH)],
                           capture_output=True, text=True)
        if r.returncode != 0:
            fail(f"{PATCH.relative_to(ROOT)} does not apply to {MODULE}@{version}: {r.stdout}{r.stderr}")
        for f in FILES:
            want = (pathlib.Path(tmp) / f).read_bytes()
            mine = COPY / f
            if not mine.exists():
                fail(f"{mine.relative_to(ROOT)} is missing")
            if mine.read_bytes() != want:
                fail(f"{mine.relative_to(ROOT)} differs from {MODULE}@{version}'s {f} with "
                     f"{PATCH.relative_to(ROOT)} applied")
    via = (f"; replaced by the fork {FORK[0]}@{FORK[1]}: {MODULE}@{version} + "
           f"{', '.join(p.name for p in FORK_PATCHES.values())} + {len(FORK_ADDED)} test file(s)"
           if forked else "")
    print(f"k8s-correctness: ok ({len(FILES)} files: {MODULE}@{version} + {PATCH.name}{via})")


if __name__ == "__main__":
    main()
