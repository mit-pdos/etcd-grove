#!/usr/bin/env python3
"""Check that a package's clients use it only through its signature.

A package's signature (`Spec/<pkg>/Sig.lean`) imports the package's internal modules
non-publicly and re-exports what clients may use, sealed (`@[no_expose]`). Lean then refuses
a client that unfolds a sealed predicate or names an internal declaration, provided the client
cannot reach the internal modules some other way. This script checks that: no module outside
the package may import a module the configuration marks `internal`, directly (with any kind of
import) or through a chain of public imports.

Linking files are exempt: a package's `Link.lean`, and the files that close a theorem over the
linked results (`Results.lean`, `Adequacy.lean`, `MainLinked.lean`) import every proof, so they
reach everything; an import chain stops at them. A non-exempt module that imports one (of any
package) is reported separately, as a warning: it reaches every package's internals through it,
which the package signatures do not cover yet (`--strict` makes it an error).

The configuration (`etc/sigs/<name>.txt`), one directive per line, `#` comments:

    inside PREFIX       a path prefix of the package's own files (repeatable)
    internal MODULE     a module only the package's own files may import (repeatable;
                        `MODULE.*` for a module and every module below it)
    exempt REGEX        a regex on a file path for the linking files

usage: etc/sig-check.py etc/sigs/raft.txt [--check] [--strict] [--verbose]
  prints every client module that reaches an internal module, with one import chain (--verbose:
  the whole chain), then the non-linking modules that import a linking file;
  --check exits 1 if there is any of the former (--strict: or of the latter).
"""
import argparse
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
SRC_DIRS = ("Code", "TrustedCode", "GeneratedProof", "ManualProof", "Spec", "Proof", "RaftWitness",
            "EtcdDeps")
IMPORT = re.compile(r"^(public\s+)?import\s+(all\s+)?(\S+)", re.M)


def load_config(path):
    inside, internal, exempt = [], [], []
    for line in pathlib.Path(path).read_text().splitlines():
        line = line.split("#", 1)[0].strip()
        if not line:
            continue
        key, _, val = line.partition(" ")
        val = val.strip()
        if key == "inside":
            inside.append(val)
        elif key == "internal":
            internal.append(val)
        elif key == "exempt":
            exempt.append(re.compile(val))
        else:
            sys.exit(f"{path}: unknown directive {key!r}")
    return inside, internal, exempt


def mod_of(p):
    return ".".join(p.relative_to(ROOT).with_suffix("").parts)


def file_of(m):
    return ROOT / (m.replace(".", "/") + ".lean")


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("config")
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--strict", action="store_true")
    ap.add_argument("--verbose", action="store_true")
    a = ap.parse_args()
    inside, internal, exempt = load_config(a.config)

    def is_internal(m):
        return any(m == i or (i.endswith(".*") and (m == i[:-2] or m.startswith(i[:-1])))
                   for i in internal)

    def is_inside(p):
        rel = p.relative_to(ROOT).as_posix()
        return any(rel.startswith(pre) for pre in inside)

    def is_exempt(p):
        rel = p.relative_to(ROOT).as_posix()
        return any(r.search(rel) for r in exempt)

    files = [p for d in SRC_DIRS if (ROOT / d).is_dir() for p in (ROOT / d).rglob("*.lean")]
    imports = {}  # module -> [(module, public)]
    for p in files:
        imports[mod_of(p)] = [(m.group(3), bool(m.group(1))) for m in IMPORT.finditer(p.read_text())]

    # chain[m] = a public-import chain from m to an internal module, or None
    memo = {}

    def reach(m, stack=()):
        if m in memo:
            return memo[m]
        if is_internal(m):
            return [m]
        if m in stack:
            return None
        memo[m] = None
        for d, public in imports.get(m, []):
            if not public or d not in imports or is_exempt(file_of(d)):
                continue
            ch = reach(d, stack + (m,))
            if ch:
                memo[m] = [m] + ch
                break
        return memo[m]

    bad, linking = [], []
    for p in sorted(files):
        if is_inside(p) or is_exempt(p):
            continue
        m = mod_of(p)
        for d, _public in imports[m]:
            if d not in imports:
                continue
            if is_exempt(file_of(d)):
                linking.append((m, d))
                continue
            ch = reach(d)
            if ch:
                bad.append((m, ch))
                break
    for m, ch in bad:
        print(f"{m}: reaches an internal module: {' -> '.join(ch) if a.verbose else ch[-1]}")
    for m, d in linking:
        print(f"warning: {m}: imports a linking file: {d}")
    print(f"{len(bad)} client module(s) reach an internal module of {a.config}; "
          f"{len(linking)} non-linking module(s) import a linking file", file=sys.stderr)
    if a.check and (bad or (a.strict and linking)):
        sys.exit(1)


if __name__ == "__main__":
    main()
