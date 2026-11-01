#!/usr/bin/env python3
"""The modules a change must rebuild: the importers, direct and indirect, of some modules.

A changed statement or definition rebuilds every module that imports its module, directly or
not; those are where a caller can break. This script lists them from the import lines of this
repository's files, without building, so that a repair finds its callers and builds only them
(`notes/spec-first-plan.md`, "The build budget") instead of running a full `lake build` to see
what fails:

    lake build $(etc/importers.py --leaves Proof/go_etcd_io/etcd/server/v3/storage/mvcc/InvStore.lean)
    etc/lean-check.py $(etc/importers.py --uses kbNoCmp_metaNone --files --direct InvStore.lean)

The targets are files or module names; `--git REV` adds the `.lean` files changed since REV
(committed or not). The output includes the targets themselves, one module per line, in an
order where a module comes after the modules it imports.

  --direct       only the direct importers (with the targets)
  --uses NAME    only the modules whose text mentions NAME (repeatable; a whole-word match, so
                 `spec` does not match `specC`): the callers that may need an edit
  --leaves       only the listed modules no other listed module imports: building them builds
                 the rest (the short command line for `lake build`)
  --files        file paths instead of module names (for `etc/lean-check.py`)
  --count        the number of modules, and of lines in their files, instead of the list

usage: etc/importers.py [--direct] [--uses NAME]... [--leaves] [--files] [--count]
                        [--git REV] TARGET...
"""

import argparse
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
IMPORT = re.compile(r"^(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?(\S+)", re.M)


def mod_of(p):
    return ".".join(p.relative_to(ROOT).with_suffix("").parts)


def file_of(m):
    return ROOT / (m.replace(".", "/") + ".lean")


def load():
    imports = {}
    for p in ROOT.rglob("*.lean"):
        rel = p.relative_to(ROOT).parts
        if rel[0].startswith("."):  # .lake, .claude worktrees
            continue
        imports[mod_of(p)] = IMPORT.findall(p.read_text(errors="replace"))
    return imports


def resolve(t, imports):
    p = pathlib.Path(t)
    if t.endswith(".lean"):
        p = (pathlib.Path.cwd() / p).resolve()
        if p.is_file():
            try:
                return mod_of(p)
            except ValueError:
                pass
        # a bare file name: the one module ending in it
        hits = [m for m in imports if m.endswith("." + p.with_suffix("").name)]
        if len(hits) == 1:
            return hits[0]
        sys.exit(f"{t}: {'no module' if not hits else 'several modules: ' + ', '.join(sorted(hits))}")
    if t in imports:
        return t
    sys.exit(f"{t}: not a module of this repository")


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("targets", nargs="*")
    ap.add_argument("--direct", action="store_true")
    ap.add_argument("--uses", action="append", default=[])
    ap.add_argument("--leaves", action="store_true")
    ap.add_argument("--files", action="store_true")
    ap.add_argument("--count", action="store_true")
    ap.add_argument("--git", metavar="REV")
    a = ap.parse_args()

    imports = load()
    targets = [resolve(t, imports) for t in a.targets]
    if a.git:
        out = subprocess.run(["git", "diff", "--name-only", a.git, "--", "*.lean"], cwd=ROOT,
                             capture_output=True, text=True, check=True).stdout
        targets += [mod_of(ROOT / f) for f in out.split() if (ROOT / f).is_file()]
    if not targets:
        sys.exit("no targets")

    importers = {}
    for m, ims in imports.items():
        for i in ims:
            importers.setdefault(i, set()).add(m)
    found = set(targets)
    frontier = list(targets)
    while frontier:
        m = frontier.pop()
        for i in importers.get(m, ()):
            if i not in found:
                found.add(i)
                if not a.direct:
                    frontier.append(i)

    if a.uses:
        word = re.compile(r"(?<![\w.'])(?:" + "|".join(map(re.escape, a.uses)) + r")(?![\w'])")
        found = {m for m in found if m in targets or word.search(file_of(m).read_text(errors="replace"))}

    # dependency order: a module after the listed modules it reaches
    order, seen = [], set()

    def visit(m):
        if m in seen:
            return
        seen.add(m)
        for i in imports.get(m, ()):
            if i in found:
                visit(i)
        order.append(m)

    for m in sorted(found):
        visit(m)

    if a.leaves:
        below = set()
        for m in found:
            stack = [i for i in imports.get(m, ()) if i in imports]
            while stack:
                i = stack.pop()
                if i not in below:
                    below.add(i)
                    stack.extend(j for j in imports.get(i, ()) if j in imports)
        order = [m for m in order if m not in below]

    if a.count:
        lines = sum(len(file_of(m).read_text(errors="replace").splitlines()) for m in order)
        print(f"{len(order)} modules, {lines} lines")
        return
    for m in order:
        print(file_of(m).relative_to(ROOT) if a.files else m)


if __name__ == "__main__":
    main()
