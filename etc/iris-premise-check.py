#!/usr/bin/env python3
"""Refuse a new Iris premise in a top-level statement that has no satisfiability witness.

A top-level statement is a `def X.spec : Prop` in a `Spec/**/TopLevelRobustness.lean` (a part's
`<Part>/Spec/...` included). Its Iris premises are its binders whose type mentions `HeapGS` or `⊢`
(an entailment or a class over the Go heap: `(Hprem : ∀ hG : HeapGS .., ⊢ X.premises ..)`,
`(Hsort : ∀ hG : HeapGS .., sort.Slice.spec ..)`). The pure-premise gate leaves these out, and one
of them, `Hctx : ∀ hG, ContextReadErrs ..`, was unsatisfiable for a month
(`notes/axiom-review/ctx-readerrs-vacuity.md`): every result taking it was vacuous.

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


def current() -> dict[tuple[str, str], str]:
    """(statement, binder) -> the binder's type, for every Iris binder."""
    res: dict[tuple[str, str], str] = {}
    for spec in spec_files():
        src = strip_comments((ROOT / spec).read_text())
        for m in SPEC_DEF.finditer(src):
            rest = src[m.end():]
            nxt = DECL.search(rest)
            body = rest[:nxt.start()] if nxt else rest
            k = body.find("∀")
            if k < 0:
                continue
            for name, ty in binders(body[k + 1:]):
                if "HeapGS" in ty or "⊢" in ty:
                    for nm in name.split():
                        res[(f"{spec}:{m.group(1)}", nm)] = " ".join(ty.split())
    return res


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
    a = ap.parse_args()
    cur = current()
    if a.list:
        for (st, b), ty in sorted(cur.items()):
            print(f"{st} {b} : {ty[:120]}")
        return 0
    base = read_baseline()
    listed = {(s, b): st for s, b, st, _ in base}
    errors = [f"{s} {b}: an Iris premise the baseline does not list (give it a witness: "
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
