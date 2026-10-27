#!/usr/bin/env python3
"""Check that a package's clients import only the package's importable modules.

Lean's visibility is per module (a declaration is `private` or public to every importer), and
`import all` is unrestricted, so a package cannot make its own shared definitions invisible to
other directories. This script enforces the boundary instead: each package lists, in
`etc/api/<pkg>.txt`, the modules other directories may import (its API). The rules:

1. a module outside the package imports (with any kind of import) only importable modules of
   the package, and never with `import all`;
2. an importable module's public imports within the package are importable themselves, so that
   nothing else of the package is reachable through them.

Linking files (`Link`, `Results`, `Adequacy*`, `MainLinked`) are exempt from rule 1: they import
every proof. A non-linking module that imports one (of any package) is reported as a warning
(`--strict`: an error): through it every package's internals are reachable.

What an importable module exposes is `etc/gen-interface.py`'s output (`interface/`): its
declarations as a client sees them, for review.

The configuration, one directive per line, `#` comments:

    inside PREFIX         a path prefix of the package's own files (repeatable)
    importable MODULE     a module other directories may import (repeatable; `MODULE.*` for every
                          module below MODULE)
    exempt REGEX          a regex on a file path for the linking files
    root MODULE           the Go package's module path below `Spec.`/`Proof.` (for
                          `etc/gen-interface.py --layout`: a spec's name is the file's path below it)

usage: etc/api-check.py etc/api/raft.txt [--check] [--strict] [--list]
  --list prints the importable modules (expanded) and exits.
"""
import argparse
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
SRC_DIRS = ("Code", "TrustedCode", "GeneratedProof", "ManualProof", "Spec", "Proof", "RaftWitness",
            "EtcdDeps")
IMPORT = re.compile(r"^(public\s+)?(meta\s+)?import\s+(all\s+)?(\S+)", re.M)


def load_config(path):
    inside, importable, exempt = [], [], []
    for line in pathlib.Path(path).read_text().splitlines():
        line = line.split("#", 1)[0].strip()
        if not line:
            continue
        key, _, val = line.partition(" ")
        val = val.strip()
        if key == "inside":
            inside.append(val)
        elif key == "importable":
            importable.append(val)
        elif key == "exempt":
            exempt.append(re.compile(val))
        elif key == "root":
            pass  # etc/gen-interface.py's (the layout checks)
        else:
            sys.exit(f"{path}: unknown directive {key!r}")
    return inside, importable, exempt


def mod_of(p):
    return ".".join(p.relative_to(ROOT).with_suffix("").parts)


def file_of(m):
    return ROOT / (m.replace(".", "/") + ".lean")


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("config")
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--strict", action="store_true")
    ap.add_argument("--list", action="store_true")
    a = ap.parse_args()
    inside, importable, exempt = load_config(a.config)

    files = [p for d in SRC_DIRS if (ROOT / d).is_dir() for p in (ROOT / d).rglob("*.lean")]
    imports = {}  # module -> [(module, public, all)]
    for p in files:
        imports[mod_of(p)] = [(m.group(4), bool(m.group(1)), bool(m.group(3)))
                              for m in IMPORT.finditer(p.read_text())]

    def is_inside(m):
        rel = file_of(m).relative_to(ROOT).as_posix()
        return any(rel.startswith(pre) for pre in inside)

    def is_exempt(m):
        rel = file_of(m).relative_to(ROOT).as_posix()
        return any(r.search(rel) for r in exempt)

    def is_importable(m):
        return any(m == i or (i.endswith(".*") and m.startswith(i[:-1])) for i in importable)

    listed = sorted(m for m in imports if is_inside(m) and is_importable(m))
    if a.list:
        print("\n".join(listed))
        return
    stale = [i for i in importable
             if not (i.endswith(".*") and any(m.startswith(i[:-1]) for m in imports)) and i not in imports]

    errors, warnings = [], []
    for m in sorted(imports):
        if is_inside(m) or is_exempt(m):
            continue
        for d, _public, al in imports[m]:
            if d not in imports:
                continue
            if is_exempt(d):
                warnings.append(f"{m}: imports a linking file: {d}")
            elif is_inside(d):
                if al:
                    errors.append(f"{m}: `import all` of a module of the package: {d}")
                elif not is_importable(d):
                    errors.append(f"{m}: imports a module that is not importable: {d}")
    for m in listed:
        for d, public, _al in imports[m]:
            if public and d in imports and is_inside(d) and not is_importable(d) and not is_exempt(d):
                errors.append(f"{m} (importable): publicly imports a module that is not importable: {d}")
    for i in stale:
        errors.append(f"{a.config}: importable {i}: no such module")
    for e in errors:
        print(e)
    for w in warnings:
        print("warning: " + w)
    print(f"{len(listed)} importable module(s); {len(errors)} error(s); "
          f"{len(warnings)} non-linking module(s) importing a linking file", file=sys.stderr)
    if a.check and (errors or (a.strict and warnings)):
        sys.exit(1)


if __name__ == "__main__":
    main()
