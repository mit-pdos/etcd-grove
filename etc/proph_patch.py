#!/usr/bin/env python3
"""Prophecy patches: changes to a project's Go code, applied before translation, that only add
prophecy variables (`primitive.NewProph`) and their resolutions (`ResolveBool`, `ResolveU64`).

usage: etc/proph_patch.py [--project NAME]... [--src NAME=DIR]...

  Checks every patch of `etc/proph-patches/<project>/` (or of the named projects) against the
  project's pinned checkout (`.lake/goose/<project>`, or DIR) and that the patches apply; exits 1
  on a violation.  etc/goose.py runs the same check before it translates.

A proof sometimes needs a prophecy the Go code does not have (to know at a read whether its answer
is the one returned).  Until prophecy erasure is settled in Lean (`notes/perennial-changes.md`,
"Prophecies in Lean only"), the prophecy goes in the Go code, as a patch kept here rather than as
a commit of the fork: `etc/proph-patches/<project>/*.patch`, unified diffs relative to the
checkout's root (`git diff` output), applied in name order to a copy of the checkout
(`.lake/goose/<project>.proph`) that etc/goose.py translates and etc/verified-code.py reads.  The
proof is of the patched code.

A patch must not change what the program does.  `primitive.NewProph()` returns an empty struct and
`ResolveBool`/`ResolveU64` are empty methods (goose-lang/primitive, `proph.go`), so a patch that
only adds such calls is a no-op in Go, provided that the calls' arguments can neither panic nor
have an effect and that the new names hide no existing one.  The check (`patch_errors`) enforces
exactly that, line by line; anything else is rejected:

- a patch only adds lines (context lines are fine; no line is removed or changed), in `.go` files
  and in `go.mod`/`go.sum` (lines of the module `github.com/goose-lang/primitive` only);
- an added Go line is blank, a `//` comment, the import `"github.com/goose-lang/primitive"`
  (alone, or `import "..."`), `NAME := primitive.NewProph()`, or `NAME.ResolveBool(ARG)` /
  `NAME.ResolveU64(ARG)`, where NAME starts with `proph` and ARG is an identifier, a literal
  (`true`, `false`, a decimal integer) or `uint64(IDENT)`;
- every NAME a patch declares or resolves occurs nowhere in the file before the patch (so it hides
  nothing, and a resolution only uses the patch's own prophecies), and a patch that adds the
  import adds it to a file that does not mention `primitive` (a file that already imports it, as
  `"github.com/goose-lang/primitive"` without a name, needs no import).

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

IMPORT_RE = re.compile(r'^(import\s+)?"github\.com/goose-lang/primitive"$')
NEW_RE = re.compile(r"^(proph\w*)\s*:=\s*primitive\.NewProph\(\)$")
ARG = r"(?:[A-Za-z_]\w*|true|false|\d+|uint64\([A-Za-z_]\w*\))"
RESOLVE_RE = re.compile(r"^(proph\w*)\.Resolve(?:Bool|U64)\((" + ARG + r")\)$")
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
    """What is wrong with the patch `patch_path` for the checkout `src` (empty: nothing)."""
    errs = []
    name = os.path.relpath(patch_path, ROOT)
    files, structural = parse(open(patch_path, encoding="utf-8").read())
    errs += [f"{name}: {l!r}: a patch only adds lines to existing files" for l in structural]
    for path, (added, removed) in files.items():
        errs += [f"{name}: {path}: removes or changes the line {l!r}" for l in removed]
        base = os.path.basename(path)
        lines = [l.strip() for l in added]
        if base in ("go.mod", "go.sum"):
            pat = GOMOD_RE if base == "go.mod" else GOSUM_RE
            errs += [f"{name}: {path}: adds {l!r}, not a line of {PRIM}"
                     for l in lines if l and not pat.match(l)]
            continue
        if not path.endswith(".go"):
            errs.append(f"{name}: {path}: not a Go file, go.mod or go.sum")
            continue
        try:
            orig = open(os.path.join(src, path), encoding="utf-8").read()
        except OSError:
            errs.append(f"{name}: {path}: no such file in {src}")
            continue
        declared, used, imports = set(), set(), False
        for l in lines:
            if l == "" or l.startswith("//"):
                continue
            if IMPORT_RE.match(l):
                imports = True
            elif m := NEW_RE.match(l):
                declared.add(m.group(1))
            elif m := RESOLVE_RE.match(l):
                used.add(m.group(1))
            else:
                errs.append(f"{name}: {path}: adds {l!r}, not a prophecy's creation or "
                            "resolution (see etc/proph_patch.py)")
        for v in sorted(declared | used):
            if re.search(r"\b" + re.escape(v) + r"\b", orig):
                errs.append(f"{name}: {path}: the name {v} already occurs in the file")
        for v in sorted(used - declared):
            errs.append(f"{name}: {path}: resolves {v}, which the patch does not create")
        mentions = re.search(r"\bprimitive\b", orig) is not None
        imported = re.search(r'^\s*(import\s+)?"github\.com/goose-lang/primitive"\s*$', orig,
                             re.M) is not None
        if imports and mentions:
            errs.append(f"{name}: {path}: adds the import of primitive to a file that already "
                        "mentions `primitive`")
        if declared and not imports and not imported:
            errs.append(f"{name}: {path}: uses primitive without importing it "
                        f"(as \"{PRIM}\", unnamed)")
    return errs


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
