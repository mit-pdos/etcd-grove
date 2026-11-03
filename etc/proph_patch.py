#!/usr/bin/env python3
"""Prophecy patches: changes to a project's Go code, applied before translation, that only add
prophecy variables (`primitive.NewProph`), their resolutions (`ResolveBool`, `ResolveU64`) and
read-only expressions.

usage: etc/proph_patch.py [--project NAME]... [--src NAME=DIR]...

  Checks every patch of `etc/proph-patches/<project>/` (or of the named projects) against the
  project's pinned checkout (`.lake/goose/<project>`, or DIR) and that the patches apply; exits 1
  on a violation.  etc/goose.py runs the same check before it translates.

A proof sometimes needs a prophecy the Go code does not have (to know at a read whether its answer
is the one returned).  Until prophecy erasure is settled in Lean (`notes/perennial-changes.md`,
"Prophecies in Lean only"), the prophecy goes in the Go code, as a patch kept here rather than as
a commit of the fork: `etc/proph-patches/<project>/*.patch`, unified diffs relative to the
project's source root (`git diff` output), applied in name order to a copy of the source
(`.lake/goose/<project>.proph`) that etc/goose.py translates and etc/verified-code.py reads.  The
proof is of the patched code.

What a patch may do, and why a proof of the patched program covers the original: the patched Go
file, with its prophecy statements erased, must be the original file as a syntax tree, and the
prophecy statements only create prophecies, resolve them with read-only expressions, and branch
on read-only conditions (etc/prophcheck/main.go, which checks it; its doc comment gives the
argument).  In short, Go's prophecy operations do nothing and a read-only expression has no
effect but may fail, so the patched program has every behavior of the original plus possibly
failing ones (a nil dereference in a resolution's argument, say), which its proof rules out.
Besides the Go files, a patch may only add the `github.com/goose-lang/primitive` lines a
`go.mod`/`go.sum` needs; it creates, deletes and renames no file.

The patched code must still compile and translate (goose reports otherwise).  A resolution's
argument is evaluated where the patch puts it: the proof sees the value at that point.
"""

import argparse
import os
import re
import shutil
import subprocess
import sys

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
PATCH_DIR = os.path.join(ROOT, "etc", "proph-patches")
PRIM = "github.com/goose-lang/primitive"
GO_TOOLCHAIN = "go1.27.3"  # etc/goose.py's

GOMOD_RE = re.compile(r"^(require\s+)?github\.com/goose-lang/primitive\s+v\S+(\s*//\s*indirect)?$")
GOSUM_RE = re.compile(r"^github\.com/goose-lang/primitive\s+v\S+\s+h1:\S+$")


def patches(project):
    """The prophecy patches of `project`, in the order they apply."""
    d = os.path.join(PATCH_DIR, project)
    if not os.path.isdir(d):
        return []
    return [os.path.join(d, f) for f in sorted(os.listdir(d)) if f.endswith(".patch")]


def parse(text):
    """The files of a unified diff, {path: ([added lines], [removed lines])}, and the structural
    changes it makes (files created, deleted, renamed or whose mode changes)."""
    files, structural, cur, new = {}, [], None, False
    for line in text.splitlines():
        if line.startswith("diff "):
            cur = None
        elif line.startswith(("new file", "deleted file", "rename ", "copy ", "similarity",
                              "old mode", "new mode")):
            structural.append(line)
        elif line.startswith("--- "):
            new = line[4:].startswith("/dev/null")
        elif line.startswith("+++ "):
            path = line[4:].split("\t")[0]
            if path == "/dev/null":
                structural.append("deletes a file")
                cur = None
                continue
            path = path[2:] if path.startswith("b/") else path
            if new:
                structural.append(f"creates {path}")
            cur = files.setdefault(path, ([], []))
        elif cur is None or line.startswith(("index ", "@@")):
            continue
        elif line.startswith("+"):
            cur[0].append(line[1:])
        elif line.startswith("-"):
            cur[1].append(line[1:])
    return files, structural


def patch_errors(patch_path, src):
    """What is wrong with the patch `patch_path` for the source `src` as a diff (empty: nothing);
    the Go files it changes are checked after it applies (`go_errors`)."""
    errs = []
    name = os.path.relpath(patch_path, ROOT)
    files, structural = parse(open(patch_path, encoding="utf-8").read())
    errs += [f"{name}: {l!r}: a patch only changes existing files" for l in structural]
    for path, (added, removed) in files.items():
        base = os.path.basename(path)
        if base in ("go.mod", "go.sum"):
            pat = GOMOD_RE if base == "go.mod" else GOSUM_RE
            errs += [f"{name}: {path}: removes or changes the line {l!r}" for l in removed]
            errs += [f"{name}: {path}: adds {l.strip()!r}, not a line of {PRIM}"
                     for l in added if l.strip() and not pat.match(l.strip())]
        elif not path.endswith(".go"):
            errs.append(f"{name}: {path}: not a Go file, go.mod or go.sum")
        elif not os.path.isfile(os.path.join(src, path)):
            errs.append(f"{name}: {path}: no such file in {src}")
    return errs


def go_files(project):
    """The Go files the patches of `project` change (relative to the source root)."""
    out = set()
    for p in patches(project):
        files, _ = parse(open(p, encoding="utf-8").read())
        out |= {f for f in files if f.endswith(".go")}
    return sorted(out)


def prophcheck():
    """etc/prophcheck, built into .lake/goose/bin."""
    bindir = os.path.join(ROOT, ".lake", "goose", "bin")
    os.makedirs(bindir, exist_ok=True)
    exe = os.path.join(bindir, "prophcheck")
    env = dict(os.environ, GOTOOLCHAIN=GO_TOOLCHAIN)
    subprocess.run(["go", "build", "-o", exe, "."], cwd=os.path.join(ROOT, "etc", "prophcheck"),
                   check=True, env=env)
    return exe


def go_errors(project, src, out):
    """What is wrong with the Go files of `out` (the patched copy of `src`) the patches change."""
    pairs = [a for f in go_files(project) for a in (os.path.join(src, f), os.path.join(out, f))]
    if not pairs:
        return []
    r = subprocess.run([prophcheck()] + pairs, capture_output=True, text=True)
    if r.returncode not in (0, 1):
        return [f"prophcheck failed: {r.stderr.strip()}"]
    return [l for l in r.stdout.splitlines() if l]


def patched_copy(project, src, dest, quiet=False):
    """`src` if `project` has no prophecy patch; else a copy of it under `dest` (made afresh,
    without `.git`) with the patches applied, after checking them (exits on a violation).  The
    patches' paths are relative to `src`.  A source in this repository (an example) is copied with
    the top-level directory that holds it (its Go module, `examples/`), the repository's other
    top-level entries linked beside it, so that the module's relative `replace`s still resolve."""
    ps = patches(project)
    if not ps:
        return src
    errs = [e for p in ps for e in patch_errors(p, src)]
    if errs:
        sys.exit("proph_patch: " + "\nproph_patch: ".join(errs))
    shutil.rmtree(dest, ignore_errors=True)
    rel = os.path.relpath(os.path.abspath(src), ROOT)
    if not rel.startswith(".."):
        top = rel.split(os.sep)[0]
        os.makedirs(dest)
        for e in os.listdir(ROOT):
            if e not in (top, ".git", ".lake"):
                os.symlink(os.path.join(ROOT, e), os.path.join(dest, e))
        shutil.copytree(os.path.join(ROOT, top), os.path.join(dest, top), symlinks=True)
        out = os.path.join(dest, rel)
    else:
        shutil.copytree(src, dest, ignore=shutil.ignore_patterns(".git"), symlinks=True)
        out = dest
    for p in ps:
        if not quiet:
            print(f"+ git apply {os.path.relpath(p, ROOT)} (in {out})", file=sys.stderr)
        r = subprocess.run(["git", "apply", "--whitespace=nowarn", p], cwd=out,
                           capture_output=True, text=True)
        if r.returncode != 0:
            sys.exit(f"proph_patch: {os.path.relpath(p, ROOT)} does not apply to {project}: "
                     f"{r.stderr.strip()}")
    errs = go_errors(project, src, out)
    if errs:
        sys.exit("proph_patch: " + "\nproph_patch: ".join(errs))
    return out


def main():
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    import importlib
    goose = importlib.import_module("goose")
    names = [p.name for p in goose.PROJECTS]
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--project", action="append", choices=names)
    ap.add_argument("--src", action="append", default=[], metavar="NAME=DIR")
    args = ap.parse_args()
    local = dict(s.partition("=")[::2] for s in args.src)
    n = 0
    for p in goose.PROJECTS:
        if (args.project and p.name not in args.project) or not patches(p.name):
            continue
        src, _ = goose.source(p, local.get(p.name), False)
        patched_copy(p.name, src, os.path.join(goose.WORK, p.name + ".proph"))
        n += len(patches(p.name))
        print(f"proph_patch: {p.name}: {len(patches(p.name))} patch(es) check and apply")
    if n == 0:
        print("proph_patch: no prophecy patches")


if __name__ == "__main__":
    main()
