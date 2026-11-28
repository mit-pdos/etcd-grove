#!/usr/bin/env python3
"""Refuse a new Iris premise in a top-level statement that has no satisfiability witness.

A top-level statement is a `def X.spec : Prop` in a `Spec/**/TopLevelRobustness.lean` (a part's
`<Part>/Spec/...` included). Its Iris premises are its binders whose type mentions `HeapGS` or `⊢`
(an entailment or a class over the Go heap: `(Hprem : ∀ hG : HeapGS .., ⊢ X.premises ..)`,
`(Hsort : ∀ hG : HeapGS .., sort.Slice.spec ..)`). The pure-premise gate leaves these out, and one
of them, `Hctx : ∀ hG, ContextReadErrs ..`, was unsatisfiable for a month
(`notes/axiom-review/ctx-readerrs-vacuity.md`): every result taking it was vacuous. An anonymous
premise, a parenthesized `(∀ G L, letI := heapAt G L; P) → …` after the `∀` binders (Dsverify's
form), is one too when it mentions `HeapGS`, `⊢` or `heapAt` (it is stated at every heap); it is
listed under the name `anon:<head>`, `<head>` the constant it applies under its `∀`s and `letI`s
(`anon:google_golang_org.grpc.InitHyp`; a later one with the same head `anon:<head>#2`, ...); `→` and
`->` both count, and the whole body is scanned (also when its first `∀` is inside a premise).
`--selftest` runs the detection's tests (`--check` runs them too).

Every such binder must be listed in `etc/iris-premise-baseline.txt`, one per line,

    <spec file>:<X> <binder> <state> <reason>

where `<state>` is `witness:<Lean name>` (a theorem, declared in the tree, from which the premise
holds at an initialized world: its proof is the build's to check; this script checks that the
declaration is there) or `unwitnessed` (grandfathered: the baseline only shrinks). `--check` fails on
an Iris binder the baseline does not list, on a named witness no `theorem` declares, and on a line
nothing needs any more (`--check --update` drops those). `--list` prints every Iris binder.
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
BASELINE = ROOT / "etc" / "iris-premise-baseline.txt"

SPEC_DEF = re.compile(r"^def\s+([A-Za-z0-9_'.]+)\.spec\s*:\s*Prop\s*:=", re.M)
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|noncomputable\s+)*"
                  r"(?:def|abbrev|theorem|lemma|instance|axiom|structure|class|end|namespace|section)\b", re.M)


def spec_files() -> list[str]:
    out = subprocess.run(["git", "ls-files", "*TopLevelRobustness.lean"], cwd=ROOT,
                         capture_output=True, text=True, check=True).stdout.split()
    return sorted(f for f in out if re.match(r"^([A-Za-z]+/)?Spec/", f))


def strip_comments(src: str) -> str:
    src = re.sub(r"/-.*?-/", "", src, flags=re.S)
    return re.sub(r"--[^\n]*", "", src)


def binders(body: str) -> list[tuple[str, str]]:
    """The top-level `(names : type)` and `[...]` binders of a statement's body, as (names, type)."""
    res, i, n = [], 0, len(body)
    while i < n:
        c = body[i]
        if c in "([{":
            close = {"(": ")", "[": "]", "{": "}"}[c]
            depth, j = 0, i
            while j < n:
                if body[j] in "([{":
                    depth += 1
                elif body[j] in ")]}":
                    depth -= 1
                    if depth == 0:
                        break
                j += 1
            inner = body[i + 1:j]
            if c == "[":
                m = re.match(r"\s*([A-Za-z0-9_'.₀-₉]+)\s*:(?!=)(.*)", inner, re.S)
                res.append((m.group(1), m.group(2)) if m else ("[" + " ".join(inner.split())[:40] + "]", inner))
            else:
                m = re.match(r"\s*([^:]+?)\s*:(?!=)(.*)", inner, re.S)
                if m:
                    res.append((m.group(1).strip(), m.group(2)))
            i = j + 1
        elif body.startswith(",", i):
            break  # the end of the `∀` binders
        else:
            i += 1
    return res


def anon_premises(body: str) -> list[tuple[str, str]]:
    """The anonymous premises of a statement's body: its depth-0 `( … )` groups followed by `→`, as
    (`anon:<head>`, type)."""
    res, depth, start = [], 0, -1
    for i, c in enumerate(body):
        if c in "([{":
            if depth == 0 and c == "(":
                start = i
            depth += 1
        elif c in ")]}":
            depth -= 1
            if depth == 0 and c == ")" and start >= 0:
                after = body[i + 1:].lstrip()
                if after.startswith("→") or after.startswith("->"):
                    inner = body[start + 1:i]
                    res.append(("anon:" + premise_head(inner), inner))
                start = -1
    return res


def premise_head(ty: str) -> str:
    """The constant a premise applies, under its leading `∀ …,` binders and `letI … ;` bindings."""
    s = ty.strip()
    while True:
        if s.startswith("∀"):
            d = 0
            for j, c in enumerate(s):
                if c in "([{":
                    d += 1
                elif c in ")]}":
                    d -= 1
                elif c == "," and d == 0:
                    s = s[j + 1:].strip()
                    break
            else:
                break
        elif s.startswith("letI") and ";" in s:
            s = s[s.index(";") + 1:].strip()
        else:
            break
    m = re.match(r"[^\s()]+", s)
    return m.group(0) if m else "?"


def first_forall(body: str) -> int:
    """The index of the statement's first `∀` at depth 0 (its outer binders), or -1."""
    depth = 0
    for i, c in enumerate(body):
        if c in "([{":
            depth += 1
        elif c in ")]}":
            depth -= 1
        elif c == "∀" and depth == 0:
            return i
    return -1


def premises_of(src: str) -> dict[tuple[str, str], str]:
    """(statement, binder) -> the binder's type, for every Iris binder of the `X.spec`s of a file's
    text (comments included; the statement key is `X`)."""
    res: dict[tuple[str, str], str] = {}
    src = strip_comments(src)
    for m in SPEC_DEF.finditer(src):
        rest = src[m.end():]
        nxt = DECL.search(rest)
        body = rest[:nxt.start()] if nxt else rest
        k = first_forall(body)
        if k >= 0:
            for name, ty in binders(body[k + 1:]):
                if "HeapGS" in ty or "⊢" in ty:
                    for nm in name.split():
                        res[(m.group(1), nm)] = " ".join(ty.split())
        seen: dict[str, int] = {}
        for name, ty in anon_premises(body):
            if "HeapGS" in ty or "⊢" in ty or "heapAt" in ty:
                # a later premise with the same head gets `#2`, `#3`, ... (it must be listed too)
                seen[name] = seen.get(name, 0) + 1
                key = name if seen[name] == 1 else f"{name}#{seen[name]}"
                res[(m.group(1), key)] = " ".join(ty.split())
    return res


def current() -> dict[tuple[str, str], str]:
    """(statement, binder) -> the binder's type, for every Iris binder."""
    res: dict[tuple[str, str], str] = {}
    for spec in spec_files():
        for (st, b), ty in premises_of((ROOT / spec).read_text()).items():
            res[(f"{spec}:{st}", b)] = ty
    return res


SELFTEST = [
    # (statement text, the binders the gate must see)
    ("def a.spec : Prop :=\n  ∀ [x : C] (H : ∀ hG : HeapGS .hasLC F, ⊢ P) (σ : state), R σ\n",
     {"H"}),
    # two anonymous premises with the same head are two keys
    ("def a.spec : Prop :=\n  ∀ [x : C],\n    (∀ G L, letI := heapAt G L; Q.InitHyp F) →\n"
     "    (∀ G L, letI := heapAt G L; Q.InitHyp F') →\n    ∀ σ, R σ\n",
     {"anon:Q.InitHyp", "anon:Q.InitHyp#2"}),
    # the ASCII arrow
    ("def a.spec : Prop :=\n  ∀ [x : C],\n    (∀ hG : HeapGS .hasLC F, ⊢ P) -> ∀ σ, R σ\n",
     {"anon:⊢"}),
    # no outer `∀`: the first `∀` is inside the premise
    ("def a.spec : Prop :=\n  (∀ hG : HeapGS .hasLC F, ⊢ P) → R\n", {"anon:⊢"}),
    # a binder that is not an Iris premise, and a ghost-allocation premise without a heap
    ("def a.spec : Prop :=\n  ∀ (n : Nat), (∀ G : GooseGlobalGS F, W G) → R n\n", set()),
]


def selftest() -> list[str]:
    errs = []
    for i, (src, want) in enumerate(SELFTEST, 1):
        got = {b for (_, b) in premises_of(src)}
        if got != want:
            errs.append(f"selftest {i}: saw {sorted(got)}, expected {sorted(want)}")
    return errs


def theorems() -> set[str]:
    out = subprocess.run(["git", "grep", "-hoE", r"^(private )?theorem [A-Za-z0-9_'.]+", "--", "*.lean"],
                         cwd=ROOT, capture_output=True, text=True).stdout
    return {line.split()[-1] for line in out.splitlines()}


def read_baseline() -> list[tuple[str, str, str, str]]:
    rows = []
    if not BASELINE.exists():
        return rows
    for ln, line in enumerate(BASELINE.read_text().splitlines(), 1):
        if not line.strip() or line.startswith("#"):
            continue
        parts = line.split(None, 3)
        if len(parts) < 4 or not (parts[2] == "unwitnessed" or parts[2].startswith("witness:")):
            sys.exit(f"iris-premise-check: {BASELINE.name}:{ln}: expected "
                     "'<statement> <binder> witness:<name>|unwitnessed <reason>'")
        rows.append((parts[0], parts[1], parts[2], parts[3]))
    return rows


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--update", action="store_true", help="with --check: drop stale baseline lines")
    ap.add_argument("--list", action="store_true")
    ap.add_argument("--selftest", action="store_true", help="only the detection's tests (--check runs them too)")
    a = ap.parse_args()
    st_errs = selftest()
    if a.selftest:
        for e in st_errs:
            print(f"iris-premise-check: {e}", file=sys.stderr)
        print(f"iris-premise-check selftest: {len(SELFTEST) - len(st_errs)}/{len(SELFTEST)} ok")
        return 1 if st_errs else 0
    cur = current()
    if a.list:
        for (st, b), ty in sorted(cur.items()):
            print(f"{st} {b} : {ty[:120]}")
        return 0
    base = read_baseline()
    listed = {(s, b): st for s, b, st, _ in base}
    errors = list(st_errs)
    errors += [f"{s} {b}: an Iris premise the baseline does not list (give it a witness: "
              f"etc/iris-premise-baseline.txt)" for (s, b) in sorted(cur) if (s, b) not in listed]
    thms = None
    for s, b, st, _ in base:
        if st.startswith("witness:") and (s, b) in cur:
            thms = thms if thms is not None else theorems()
            if st[len("witness:"):] not in thms:
                errors.append(f"{s} {b}: its witness {st[len('witness:'):]} is declared by no theorem")
    stale = [(s, b) for s, b, _, _ in base if (s, b) not in cur]
    if stale and a.update and not errors:
        keep = [ln for ln in BASELINE.read_text().splitlines()
                if not ln.strip() or ln.startswith("#") or tuple(ln.split(None, 3)[:2]) not in stale]
        BASELINE.write_text("\n".join(keep) + "\n")
        print(f"iris-premise-check: dropped {len(stale)} stale baseline line(s)")
        stale = []
    errors += [f"{s} {b}: in the baseline, but no statement takes it (--check --update)" for s, b in stale]
    for e in errors:
        print(f"iris-premise-check: {e}", file=sys.stderr)
    if not errors:
        print(f"iris-premise-check: {len(cur)} Iris premises, all listed")
    return 1 if (errors and a.check) else 0


if __name__ == "__main__":
    sys.exit(main())
