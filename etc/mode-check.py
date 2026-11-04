#!/usr/bin/env python3
"""Count the auth-mode divergence outside the auth component (the auth component's stage 2, D2).

The server reaches auth through one slot, `AuthC` (`AuthComp.lean`): `off`, or `on γa`. What
still branches on a mode, or comes in an off/on pair, outside that slot is counted here, per kind
and per package, so that the refactor's progress is tracked and no new divergence comes in:

    match-mode  a `match` or `if` on a mode in a definition (`def`/`abbrev`/`instance`) outside
                `AuthComp.lean`: `match on`, `match M`, `match C`, `match K`, a `match` on an
                `authMode`, an `if` on an `authOn`
    twin        a declaration named `X.specOn`, `X.specOnR`, `X.specM`, `X.wp_proofOn` or
                `X.wp_proofM` outside `ModeSpecs.lean` (whose corollaries restate the merged specs)
    lit-mode    a literal `true`/`false` argument to a definition whose first explicit binder is
                `(on : Bool)` (the mode chosen by hand rather than by the slot, `C.isOn`)

`(C : AuthC)` binders are not counted: the slot is the point. Scope: the server
(`go_etcd_io/etcd/server/v3/etcdserver`, `api/v3rpc` included), `client/v3` and the examples
(`etcdstart` included), Spec and Proof; comments and docstrings are stripped first. The package of
a file is its directory without the `Spec`/`Proof` level.

Each finding is classified in `etc/mode-allow.txt` (`KIND CLASS REGEX  # why`, the regex searched in
`FILE::DECLARATION::TEXT`; the classes: model, flag, corollary, pair, bridge, unmoved); a finding
that no line classifies fails the check. The counts are checked against `etc/mode-baseline.txt`,
which may only go down: a ratchet (every later stage of the refactor lowers it).

usage:
    etc/mode-check.py                  totals per kind and class, then per package
    etc/mode-check.py --kind KIND      ... and every finding of KIND (file:line: decl: text [class])
    etc/mode-check.py --check          exit 1 on an unclassified finding, or a (kind, package)
                                       count above etc/mode-baseline.txt; decreases are reported
    etc/mode-check.py --check --update rewrite the baseline (after a decrease)

Reads the sources only; needs no build.
"""
from __future__ import annotations

import argparse
import importlib.util
import os
import re
import sys
from collections import Counter, defaultdict

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BASELINE = os.path.join(ROOT, "etc", "mode-baseline.txt")
ALLOW = os.path.join(ROOT, "etc", "mode-allow.txt")

_spec = importlib.util.spec_from_file_location("bounds_check", os.path.join(ROOT, "etc", "bounds-check.py"))
_bc = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_bc)
strip_comments = _bc.strip_comments

SCOPE = [
    "go_etcd_io/etcd/server/v3/etcdserver",
    "go_etcd_io/etcd/client/v3",
    "github_com/mit_pdos/etcd_grove/examples",
]
KIND_NAMES = ["match-mode", "twin", "lit-mode"]
CLASSES = ["model", "flag", "corollary", "pair", "bridge", "unmoved"]

DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|partial|unsafe)\s+)*"
                  r"(def|abbrev|instance|theorem|lemma|structure|inductive|opaque|axiom|class)\b\s*([^\s:(\[{]*)",
                  re.M)
MATCH_MODE = re.compile(r"\bmatch\s+(?:on|M|C|K|[\w.]*\.authMode|[\w.]*authMode)\s+with\b"
                        r"|\bif\s+(?:h\w*\s*:\s*)?[\w.]*\.authOn\b")
TWIN = re.compile(r"\.(specOn|specOnR|specM|wp_proofOn|wp_proofM)$")
ON_BOOL_DEF = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?(?:def|abbrev)\s+([\w.']+)\s*\(on\s*:\s*Bool\)", re.M)


def files():
    for sub in ("Spec", "Proof"):
        for sc in SCOPE:
            d = os.path.join(ROOT, sub, sc)
            for dirpath, _, fs in os.walk(d):
                for f in sorted(fs):
                    if f.endswith(".lean"):
                        path = os.path.join(dirpath, f)
                        rel = os.path.relpath(path, ROOT)
                        pkg = re.sub(r"^(Spec|Proof)/", "", os.path.relpath(dirpath, ROOT))
                        yield path, rel, pkg


def decls(code: str):
    """(start offset, kind, name) of each top-level declaration."""
    return [(m.start(), m.group(1), m.group(2)) for m in DECL.finditer(code)]


def decl_at(ds, off):
    cur = (0, "", "")
    for d in ds:
        if d[0] > off:
            break
        cur = d
    return cur


def load_allow():
    res = []
    if os.path.exists(ALLOW):
        for n, line in enumerate(open(ALLOW, encoding="utf-8"), 1):
            line = line.split("#", 1)[0].strip()
            if not line:
                continue
            kind, cls, rx = line.split(None, 2)
            if kind not in KIND_NAMES and kind != "*":
                sys.exit(f"mode-check: {ALLOW}:{n}: unknown kind {kind}")
            if cls not in CLASSES:
                sys.exit(f"mode-check: {ALLOW}:{n}: unknown class {cls}")
            res.append((kind, cls, re.compile(rx.strip())))
    return res


def scan():
    allow = load_allow()
    srcs = [(path, rel, pkg, strip_comments(open(path, encoding="utf-8").read())) for path, rel, pkg in files()]
    onbool = set()
    for _, _, _, code in srcs:
        for m in ON_BOOL_DEF.finditer(code):
            onbool.add(m.group(1).split(".")[-1])
    lit = re.compile(r"\b(" + "|".join(sorted(map(re.escape, onbool))) + r")(?:\s*\(\w+\s*:=\s*\w+\))*\s+(true|false)\b") if onbool else None
    findings = []  # (kind, pkg, rel, line, decl, text, class or None)

    def add(kind, pkg, rel, code, off, decl, text):
        key = f"{rel}::{decl}::{text}"
        cls = next((c for k, c, rx in allow if (k == kind or k == "*") and rx.search(key)), None)
        findings.append((kind, pkg, rel, code.count("\n", 0, off) + 1, decl, text, cls))

    for path, rel, pkg, code in srcs:
        ds = decls(code)
        base = os.path.basename(rel)
        if base != "AuthComp.lean":
            for m in MATCH_MODE.finditer(code):
                _, kind, name = decl_at(ds, m.start())
                if kind in ("def", "abbrev", "instance"):
                    add("match-mode", pkg, rel, code, m.start(), name, " ".join(m.group(0).split()))
        if base != "ModeSpecs.lean":
            for off, kind, name in ds:
                if TWIN.search(name):
                    add("twin", pkg, rel, code, off, name, f"{kind} {name}")
        if lit:
            for m in lit.finditer(code):
                # the definition's own header is no use of it
                line_start = code.rfind("\n", 0, m.start()) + 1
                if ON_BOOL_DEF.match(code[line_start:code.find("\n", m.start())]):
                    continue
                _, _, name = decl_at(ds, m.start())
                add("lit-mode", pkg, rel, code, m.start(), name, " ".join(m.group(0).split()))
    return findings


def read_baseline() -> Counter:
    base: Counter = Counter()
    if os.path.exists(BASELINE):
        for line in open(BASELINE, encoding="utf-8"):
            line = line.split("#", 1)[0].strip()
            if line:
                kind, pkg, n = line.split()
                base[(kind, pkg)] = int(n)
    return base


def write_baseline(counts: Counter) -> None:
    with open(BASELINE, "w", encoding="utf-8") as f:
        f.write("# etc/mode-check.py's baseline: KIND PACKAGE COUNT (the auth component's stage 2, D2).\n")
        f.write("# Counts may only go down; rewrite with `etc/mode-check.py --check --update`.\n")
        for (kind, pkg), n in sorted(counts.items(), key=lambda kv: (KIND_NAMES.index(kv[0][0]), kv[0][1])):
            if n:
                f.write(f"{kind} {pkg} {n}\n")


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--update", action="store_true")
    ap.add_argument("--kind", choices=KIND_NAMES)
    args = ap.parse_args()
    findings = scan()
    counts: Counter = Counter((k, p) for k, p, *_ in findings)
    unclassified = [f for f in findings if f[6] is None]

    if args.check:
        base = read_baseline()
        worse = [(k, base[k], counts[k]) for k in sorted(set(counts) | set(base)) if counts[k] > base[k]]
        better = [(k, base[k], counts[k]) for k in sorted(base) if counts[k] < base[k]]
        for kind, pkg, rel, ln, decl, text, _ in unclassified:
            print(f"mode: unclassified {kind}: {rel}:{ln}: {decl}: {text} (add it to etc/mode-allow.txt)")
        if args.update:
            if unclassified:
                print("mode: FAILED (classify the findings above first)")
                return 1
            write_baseline(counts)
            print(f"mode: baseline rewritten ({sum(counts.values())} in {len(+counts)} rows)")
            return 0
        for (kind, pkg), b, n in worse:
            print(f"mode: {kind} in {pkg}: {n}, baseline {b}" + (" (new)" if b == 0 else ""))
        for (kind, pkg), b, n in better:
            print(f"mode: {kind} in {pkg}: {n}, down from {b} (run --check --update)")
        total, btotal = sum(counts.values()), sum(base.values())
        if worse or unclassified:
            print(f"mode: FAILED ({total} against the baseline's {btotal}; "
                  f"`etc/mode-check.py --kind KIND` lists them)")
            return 1
        print(f"mode: ok ({total}, baseline {btotal})")
        return 0

    print("per kind and class:")
    for k in KIND_NAMES:
        byc = Counter(f[6] or "UNCLASSIFIED" for f in findings if f[0] == k)
        print(f"  {k:11} {sum(byc.values()):5}  " + ", ".join(f"{c} {n}" for c, n in sorted(byc.items())))
    print("\nper package:")
    bypkg: dict = defaultdict(Counter)
    for (kind, pkg), n in counts.items():
        bypkg[pkg][kind] = n
    for pkg in sorted(bypkg, key=lambda p: -sum(bypkg[p].values())):
        row = ", ".join(f"{k} {bypkg[pkg][k]}" for k in KIND_NAMES if k in bypkg[pkg])
        print(f"  {sum(bypkg[pkg].values()):5}  {pkg}: {row}")
    if args.kind:
        print(f"\n{args.kind}:")
        for kind, pkg, rel, ln, decl, text, cls in findings:
            if kind == args.kind:
                print(f"  {rel}:{ln}: {decl}: {text} [{cls or 'UNCLASSIFIED'}]")
    return 0


if __name__ == "__main__":
    sys.exit(main())
