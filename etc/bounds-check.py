#!/usr/bin/env python3
"""Count the bound reasoning that leaks out of its owners (`notes/bounds-plan.md`, B0).

The plan's rule: each bound (live threads, `RWMutex` reader slots, lifetime counters, sizes) is
reasoned about in one place -- the adequacy theorem, the owner of the bounded object, or one
predicate per boundary -- and no spec in between mentions it. This script counts, per kind and
per Go package, the places that do not yet follow the rule, so that the plan's progress can be
tracked and new leaks are refused:

    spec-thread    `threadBound` in a Spec file's code
    spec-receipt   `receiptBound` in a Spec file's code
    spec-readers   `actualMaxReaders` in a Spec file's code
    spec-cfg       a server-configuration scope premise in a Spec file (`etcdMaxRequestBytesOk`,
                   `maxTxnOpsOk`), to be bundled (B5's `cfgScopeOk`)
    spec-rev       a revision bound restated in a Spec file (`rev + k < 2 ^ 63`, B4)
    stock          a counted stock of a named resource, `[∗list] _ ∈ List.replicate n (), R` with
                   `R` a name of two characters or more (Spec and Proof; a single-letter `R` or
                   `iprop(..)` is a generic lemma's variable): the reader slots B2 moves into
                   thread pools, and the other stocks B0's inventory sorts
    wire-unfold    `unfold`/`simp` of `wireSlack` or `grpcMsgMax` in a Proof file (B5's generic
                   message-size lemma)

Only code counts: comments and docstrings are stripped first. The package of a file is its
directory (below `Spec/` or `Proof/`, with a part's root prefixed, `RaftWitness/...`); `stock` counts
Spec and Proof together, `wire-unfold` Proof only. (Length literals in specs, `.length ≤ 2 ^ k`,
were counted until 2026-11-01: each is a library's exact precondition on its input, which naming
would not simplify; `notes/bounds-plan.md`, B5.)

Owners, whose own invariants legitimately do this reasoning, are listed in `etc/bounds-allow.txt`
(`KIND REGEX  # why`, the regex searched in the file's path): their matches are not counted.

usage:
    etc/bounds-check.py                  totals per kind, then per package
    etc/bounds-check.py --kind KIND      ... and every match of KIND (file:line: text)
    etc/bounds-check.py --check          exit 1 if a (kind, package) count exceeds
                                         etc/bounds-baseline.txt or is new; decreases are reported
    etc/bounds-check.py --check --update rewrite the baseline (after a decrease, or an increase
                                         that is meant: say why in the commit)

Reads the sources only; needs no build.
"""
from __future__ import annotations

import argparse
import os
import re
import sys
from collections import Counter, defaultdict

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BASELINE = os.path.join(ROOT, "etc", "bounds-baseline.txt")
ALLOW = os.path.join(ROOT, "etc", "bounds-allow.txt")

# (kind, regex, which trees: "spec", "proof" or "both")
KINDS: list[tuple[str, re.Pattern[str], str]] = [
    ("spec-thread", re.compile(r"\bthreadBound\b"), "spec"),
    ("spec-receipt", re.compile(r"\breceiptBound\b"), "spec"),
    ("spec-readers", re.compile(r"\bactualMaxReaders\b"), "spec"),
    ("spec-cfg", re.compile(r"\b(etcdMaxRequestBytesOk|maxTxnOpsOk)\b"), "spec"),
    ("spec-rev", re.compile(r"\brev\s*\+\s*\d+\s*<\s*2\s*\^\s*63\b"), "spec"),
    ("stock", re.compile(r"\[∗\s*list\]\s*\S+\s*∈\s*List\.replicate\s+(?:\([^()]*(?:\([^()]*\)[^()]*)*\)|\S+)"
                         r"\s*\(\),\s*(?!iprop\b)(?:\(\s*)?([A-Za-z_][\w.']*[\w'][\w.']*)"), "both"),
    ("shared-limit", re.compile(r"\.length\s*(<|≤)\s*2\s*\^\s*2[678]\b"), "spec"),
    ("wire-unfold", re.compile(r"\b(unfold|simp|dsimp|rw)\b[^\n]*\b(wireSlack|grpcMsgMax)\b"), "proof"),
]
KIND_NAMES = [k for k, _, _ in KINDS]


def strip_comments(src: str) -> str:
    """Blank out Lean comments (`-- ...` and nested `/- ... -/`, docstrings included), keeping
    the line structure; string literals are kept (a `--` inside one is not a comment)."""
    out: list[str] = []
    i, n, depth = 0, len(src), 0
    in_str = False
    while i < n:
        c = src[i]
        if depth:
            if src.startswith("/-", i):
                depth += 1; out.append("  "); i += 2; continue
            if src.startswith("-/", i):
                depth -= 1; out.append("  "); i += 2; continue
            out.append("\n" if c == "\n" else " "); i += 1; continue
        if in_str:
            out.append(c)
            if c == "\\" and i + 1 < n:
                out.append(src[i + 1]); i += 2; continue
            if c == '"':
                in_str = False
            i += 1; continue
        if c == '"':
            in_str = True; out.append(c); i += 1; continue
        if src.startswith("/-", i):
            depth = 1; out.append("  "); i += 2; continue
        if src.startswith("--", i):
            j = src.find("\n", i)
            j = n if j < 0 else j
            out.append(" " * (j - i)); i = j; continue
        out.append(c); i += 1
    return "".join(out)


def trees() -> list[tuple[str, str, str]]:
    """(directory, tree kind "spec"/"proof", part prefix) of every Spec/Proof tree."""
    res = []
    for part in ["", "RaftWitness"]:
        for sub, kind in (("Spec", "spec"), ("Proof", "proof")):
            d = os.path.join(ROOT, part, sub)
            if os.path.isdir(d):
                res.append((d, kind, part))
    return res


def load_allow() -> list[tuple[str, re.Pattern[str]]]:
    res = []
    if os.path.exists(ALLOW):
        for line in open(ALLOW, encoding="utf-8"):
            line = line.split("#", 1)[0].strip()
            if not line:
                continue
            kind, rx = line.split(None, 1)
            if kind not in KIND_NAMES and kind != "*":
                sys.exit(f"bounds-check: {ALLOW}: unknown kind {kind}")
            res.append((kind, re.compile(rx.strip())))
    return res


def scan():
    allow = load_allow()
    counts: Counter[tuple[str, str]] = Counter()
    matches: dict[str, list[str]] = defaultdict(list)
    for d, tkind, part in trees():
        for dirpath, _, files in os.walk(d):
            for f in sorted(files):
                if not f.endswith(".lean"):
                    continue
                path = os.path.join(dirpath, f)
                rel = os.path.relpath(path, ROOT)
                pkg = os.path.join(part, os.path.relpath(dirpath, os.path.dirname(d)))
                # the package without its Spec/Proof level: Spec/a/b and Proof/a/b are one package
                pkg = re.sub(r"(^|/)(Spec|Proof)(/|$)", r"\1", pkg, count=1).rstrip("/") or "."
                code = strip_comments(open(path, encoding="utf-8").read())
                lines = code.split("\n")
                for kind, rx, where in KINDS:
                    if where != "both" and where != tkind:
                        continue
                    if any((k == kind or k == "*") and a.search(rel) for k, a in allow):
                        continue
                    for m in rx.finditer(code):
                        if kind == "stock" and len(m.group(1)) < 2:
                            continue
                        ln = code.count("\n", 0, m.start()) + 1
                        counts[(kind, pkg)] += 1
                        matches[kind].append(f"{rel}:{ln}: {' '.join(m.group(0).split())[:160]}")
    return counts, matches


def read_baseline() -> Counter[tuple[str, str]]:
    base: Counter[tuple[str, str]] = Counter()
    if os.path.exists(BASELINE):
        for line in open(BASELINE, encoding="utf-8"):
            line = line.split("#", 1)[0].strip()
            if line:
                kind, pkg, n = line.split()
                base[(kind, pkg)] = int(n)
    return base


def write_baseline(counts: Counter[tuple[str, str]]) -> None:
    with open(BASELINE, "w", encoding="utf-8") as f:
        f.write("# etc/bounds-check.py's baseline: KIND PACKAGE COUNT (notes/bounds-plan.md, B0).\n")
        f.write("# Counts may only go down; rewrite with `etc/bounds-check.py --check --update`.\n")
        for (kind, pkg), n in sorted(counts.items(), key=lambda kv: (KIND_NAMES.index(kv[0][0]), kv[0][1])):
            if n:
                f.write(f"{kind} {pkg} {n}\n")


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--update", action="store_true")
    ap.add_argument("--kind", choices=KIND_NAMES)
    args = ap.parse_args()
    counts, matches = scan()

    if args.check:
        base = read_baseline()
        worse = [(k, b, counts[k]) for k in sorted(set(counts) | set(base)) if counts[k] > base[k]
                 for b in [base[k]]]
        better = [(k, base[k], counts[k]) for k in sorted(base) if counts[k] < base[k]]
        if args.update:
            write_baseline(counts)
            print(f"bounds: baseline rewritten ({sum(counts.values())} in {len(+counts)} rows)")
            return 0
        for (kind, pkg), b, n in worse:
            print(f"bounds: {kind} in {pkg}: {n}, baseline {b}" + (" (new)" if b == 0 else ""))
        for (kind, pkg), b, n in better:
            print(f"bounds: {kind} in {pkg}: {n}, down from {b} (run --check --update)")
        total, btotal = sum(counts.values()), sum(base.values())
        if worse:
            print(f"bounds: FAILED ({total} against the baseline's {btotal}; "
                  f"`etc/bounds-check.py --kind KIND` lists them)")
            return 1
        print(f"bounds: ok ({total}, baseline {btotal})")
        return 0

    tot = Counter()
    for (kind, _), n in counts.items():
        tot[kind] += n
    print("per kind:")
    for k in KIND_NAMES:
        npk = sum(1 for (kk, _), n in counts.items() if kk == k and n)
        print(f"  {k:13} {tot[k]:6}  in {npk} packages")
    print("\nper package (kinds with a count):")
    bypkg: dict[str, dict[str, int]] = defaultdict(dict)
    for (kind, pkg), n in counts.items():
        bypkg[pkg][kind] = n
    for pkg in sorted(bypkg, key=lambda p: -sum(bypkg[p].values())):
        row = ", ".join(f"{k} {bypkg[pkg][k]}" for k in KIND_NAMES if k in bypkg[pkg])
        print(f"  {sum(bypkg[pkg].values()):5}  {pkg}: {row}")
    if args.kind:
        print(f"\n{args.kind}:")
        for m in matches[args.kind]:
            print("  " + m)
    return 0


if __name__ == "__main__":
    sys.exit(main())
