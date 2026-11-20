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


def fail(msg):
    print(f"k8s-correctness: FAILED: {msg}")
    sys.exit(1)


def pinned_version():
    gomod = (MODDIR / "go.mod").read_text()
    m = re.search(r"^\s*" + re.escape(MODULE) + r"\s+(\S+)", gomod, re.M)
    if not m:
        fail(f"{MODULE} not required in {MODDIR / 'go.mod'}")
    for r in re.finditer(r"^\s*replace\s+" + re.escape(MODULE) + r"\b", gomod, re.M):
        fail(f"{MODULE} is replaced in go.mod: the copy's provenance is the required version")
    return m.group(1)


def module_dir(version):
    env = dict(os.environ, GOWORK="off", GOFLAGS="-mod=mod")
    out = subprocess.run(["go", "mod", "download", "-json", f"{MODULE}@{version}"], cwd=MODDIR,
                         env=env, capture_output=True, text=True)
    if out.returncode != 0:
        fail(f"go mod download {MODULE}@{version}: {out.stderr.strip() or out.stdout.strip()}")
    d = json.loads(out.stdout).get("Dir")
    if not d:
        fail(f"go mod download {MODULE}@{version}: no Dir")
    return pathlib.Path(d) / PKG


def main():
    version = pinned_version()
    src = module_dir(version)
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
    print(f"k8s-correctness: ok ({len(FILES)} files: {MODULE}@{version} + {PATCH.name})")


if __name__ == "__main__":
    main()
