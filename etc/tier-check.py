#!/usr/bin/env python3
"""Check the import tiers: specs never import proofs (CLAUDE.md, "Import tiers").

Every module of this repository is in one of five tiers, and a module imports only modules of
its own tier or lower, except that a spec may import defs (they are its vocabulary) and defs may
import specs:

    base     the translations and the framework (`Code/`, `GeneratedProof/`, `TrustedCode/`,
             `ManualProof/`, `GooseLang/`, `Robustness/`, `SpecPlan/`, ...): every module that is
             not under a `Spec`/`Proof` root (`Spec/`, `Proof/`, a part's `<Part>/Spec/`, ...)
    spec     a module under a `Spec` root
    defs     a module under a `Proof` root that is neither a proof file nor a linking module:
             shared definitions, invariants, lemmas (`Defs`, `Inv*`, `Base`, `SpecResults`, ...)
    proof    a `Proof` module declaring `theorem`/`axiom <F>.wp_proof` or a variant of it
             (`<F>.wp_proofSnapM`, `<F>.wp_proof_crash`: one function's proof)
    linking  a `Proof` module named `Link`, `Results`, `TopLevelRobustness`, `*Linked` (`Linked`, `MainLinked`,
             `TracedLinked`, ...) or `Adequacy*`, or listed in `etc/tier-linking.txt` (a module
             that composes linked results under another name)

The rule: a spec, defs or proof module never imports a proof or linking module (only linking
modules do), and a base module imports no spec, defs, proof or linking module. A proof file thus
sees its callees through their specs only, and an edit to one proof rebuilds only the linking
modules above it, never a spec or another proof.

The violations left are listed in `etc/tier-baseline.txt` (`IMPORTER IMPORTED`, one edge per
line, with its kind in a comment). `--check` refuses a violation not listed there and reports the
listed ones that are gone; `--check --update` rewrites the baseline without them (it only
shrinks: a new violation is fixed, not listed).

usage:
    etc/tier-check.py                   counts per edge kind, then every violation
    etc/tier-check.py --tier MODULE...  the tier of each module (a file path or a module name), its
                                        direct importers, and its cone (the modules importing it,
                                        directly or not, by tier: what an edit to it rebuilds)
    etc/tier-check.py --check [--update]

Reads the sources only; needs no build.
"""
from __future__ import annotations

import argparse
import os
import re
import sys
from collections import Counter

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.dont_write_bytecode = True
sys.path.insert(0, os.path.join(ROOT, "etc"))
from proof_roots import PART_ROOTS  # noqa: E402

BASELINE = os.path.join(ROOT, "etc", "tier-baseline.txt")
LINKING_LIST = os.path.join(ROOT, "etc", "tier-linking.txt")
SKIP_DIRS = {".lake", ".claude", ".git", "old", "examples", "third_party", "notes", "issues",
             "nonissues", "interface", "etc"}
TIERS = ["base", "spec", "defs", "proof", "linking"]
SPEC_ROOTS = tuple(["Spec."] + [f"{r}.Spec." for r in PART_ROOTS])
PROOF_ROOTS = tuple(["Proof."] + [f"{r}.Proof." for r in PART_ROOTS])
LINKING_NAMES = {"Link", "Results", "TopLevelRobustness"}
IMPORT = re.compile(r"^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?(\S+)", re.M)
WP_PROOF = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable)\s+)*(?:theorem|axiom)\s+"
    r"\S*\bwp_proof\w*", re.M)
COMMENT = re.compile(r"/-.*?-/|--[^\n]*", re.S)


def load():
    """{module: (text, imports)} for every module of this repository."""
    mods = {}
    for dirpath, dirs, files in os.walk(ROOT):
        rel = os.path.relpath(dirpath, ROOT)
        if rel == ".":
            dirs[:] = [d for d in dirs if d not in SKIP_DIRS and not d.startswith(".")]
        for f in files:
            if f.endswith(".lean"):
                p = os.path.join(dirpath, f)
                m = os.path.relpath(p, ROOT)[:-5].replace(os.sep, ".")
                with open(p, errors="replace") as fh:
                    mods[m] = fh.read()
    return mods


def linking_list():
    out = set()
    if os.path.exists(LINKING_LIST):
        for line in open(LINKING_LIST):
            line = line.split("#", 1)[0].strip()
            if line:
                out.add(line)
    return out


def tier(m, text, extra_linking):
    if m.startswith(SPEC_ROOTS):
        return "spec"
    if not m.startswith(PROOF_ROOTS):
        return "base"
    base = m.rsplit(".", 1)[-1]
    if base in LINKING_NAMES or base.endswith("Linked") or base.startswith("Adequacy") or m in extra_linking:
        return "linking"
    if WP_PROOF.search(COMMENT.sub("", text)):
        return "proof"
    return "defs"


def violation(src, dst):
    """Whether an import of a `dst` module by a `src` module breaks the tiers."""
    if src == "linking":
        return False
    if src == "base":
        return dst != "base"
    return dst in ("proof", "linking")


def classify():
    mods = load()
    extra = linking_list()
    for m in sorted(extra):
        if m not in mods:
            sys.exit(f"tier: {LINKING_LIST}: {m} is not a module of this repository")
    tiers = {m: tier(m, t, extra) for m, t in mods.items()}
    edges = []
    for m, t in mods.items():
        IMPORTS[m] = [i for i in IMPORT.findall(t) if i in mods]
        for i in IMPORTS[m]:
            if violation(tiers[m], tiers[i]):
                edges.append((m, i, f"{tiers[m]}->{tiers[i]}"))
    return tiers, sorted(edges)


IMPORTS: dict[str, list[str]] = {}


def describe(m, tiers):
    """A module's tier, its direct importers, and its cone (every module importing it) by tier."""
    importers = {}
    for s, ims in IMPORTS.items():
        for i in ims:
            importers.setdefault(i, set()).add(s)
    cone, stack = set(), [m]
    while stack:
        for i in importers.get(stack.pop(), ()):
            if i not in cone:
                cone.add(i)
                stack.append(i)
    c = Counter(tiers[i] for i in cone)
    print(f"{tiers.get(m, '?')}  {m}: cone {len(cone)} ("
          + ", ".join(f"{t} {c[t]}" for t in TIERS if c[t]) + ")")
    for i in sorted(importers.get(m, ())):
        print(f"    imported by {tiers[i]:8} {i}")


def read_baseline():
    out = {}
    if os.path.exists(BASELINE):
        for line in open(BASELINE):
            body = line.split("#", 1)[0].split()
            if len(body) == 2:
                out[(body[0], body[1])] = line.rstrip("\n")
    return out


HEADER = """\
# The import-tier violations left (etc/tier-check.py; CLAUDE.md, "Import tiers"): IMPORTER IMPORTED,
# kind in the comment. Only shrinks: `etc/tier-check.py --check --update` after a fix.
"""


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--update", action="store_true")
    ap.add_argument("--tier", nargs="+", metavar="MODULE")
    a = ap.parse_args()
    tiers, edges = classify()
    if a.tier:
        for t in a.tier:
            m = t[:-5].replace(os.sep, ".") if t.endswith(".lean") else t
            if m not in tiers:
                sys.exit(f"tier: {t}: not a module of this repository")
            describe(m, tiers)
        return 0
    kinds = Counter(k for _, _, k in edges)
    summary = ", ".join(f"{k} {n}" for k, n in sorted(kinds.items())) or "none"
    if not a.check:
        print(f"tiers: {Counter(tiers.values())}")
        print(f"violations: {len(edges)} ({summary})")
        for s, d, k in edges:
            print(f"  {k:16} {s} -> {d}")
        return 0
    base = read_baseline()
    cur = {(s, d): k for s, d, k in edges}
    # no baseline yet: --update writes the first one
    new = [(s, d, k) for (s, d), k in sorted(cur.items())
           if (s, d) not in base and (os.path.exists(BASELINE) or not a.update)]
    gone = sorted(set(base) - set(cur))
    if new:
        print(f"tier: FAILED: {len(new)} import(s) break the tiers (CLAUDE.md, \"Import tiers\"):")
        for s, d, k in new:
            print(f"  {k:16} {s} -> {d}")
        return 1
    if a.update:
        with open(BASELINE, "w") as fh:
            fh.write(HEADER)
            for (s, d), k in sorted(cur.items()):
                fh.write(f"{s} {d}  # {k}\n")
        print(f"tier: baseline rewritten: {len(cur)} violations ({len(gone)} gone)")
        return 0
    for s, d in gone:
        print(f"tier: fixed (rerun with --check --update): {s} -> {d}")
    print(f"tier: ok, {len(cur)} known violations ({summary})"
          + (f", {len(gone)} fewer than the baseline" if gone else ""))
    return 0


if __name__ == "__main__":
    sys.exit(main())
