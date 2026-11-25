#!/usr/bin/env python3
"""Check that every top-level statement has a satisfiability witness of its premises.

A top-level statement is a `def X.spec : Prop` in a `Spec/**/TopLevelRobustness.lean` (a part's
`<Part>/Spec/...` included). Its witness is

    theorem X.premisesSat : premise_sat% X.spec [without [h, ...]] := ...

in the matching `Proof/.../TopLevelWitness.lean` (`Spec/` replaced by `Proof/`): the premises,
together with `Robust`'s own antecedents, can all hold (`Robustness/PremiseSat.lean`). The Lean build
checks the proof; this script checks, reading the sources only, that the theorem is there, and
that what it leaves out is known:

* every binder named in a `without` list, and every statement with no witness yet, is listed in
  `etc/premise-witness-baseline.txt`, one per line, `<statement> <binder|*> <class> <reason>`, where
  `*` stands for "no witness yet" and the class is one of
  - `opaque`: an opaque or axiom-declared proposition (an environment claim): no Lean proof can
    establish it, so it is left out for good; its meaning is in the axioms that consume it;
  - `pending-b`: a fact about what Go computes (member ids, boot logs) stated over definitions
    Lean cannot evaluate yet (the opaque `ccDecodeV1`, no `memberIdOf`);
  - `pending`: to be witnessed;
  - `draft`: a statement not instantiable yet;
* a premise mentioning `HeapGS` or `Iris` (an Iris contract) is left out by `premise_sat%`
  itself, with no baseline line: those are being made per-function axioms (rule 36).

`--check` fails on anything unlisted, and on a baseline line nothing needs any more (run
`--check --update` to drop those: the baseline only shrinks). `--list` prints each statement and
its state.
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
BASELINE = ROOT / "etc" / "premise-witness-baseline.txt"
CLASSES = {"opaque", "pending-b", "pending", "draft"}

SPEC_DEF = re.compile(r"^def\s+([A-Za-z0-9_'.]+)\.spec\s*:\s*Prop\b", re.M)
WITNESS = re.compile(
    r"theorem\s+([A-Za-z0-9_'.]+)\.premisesSat\s*:\s*premise_sat%\s+([A-Za-z0-9_'.]+)\.spec"
    r"(?:\s+without\s*\[([^\]]*)\])?")


def spec_files() -> list[str]:
    out = subprocess.run(["git", "ls-files", "*TopLevelRobustness.lean"], cwd=ROOT,
                         capture_output=True, text=True, check=True).stdout.split()
    return sorted(f for f in out if re.match(r"^([A-Za-z]+/)?Spec/", f))


def witness_file(spec: str) -> str:
    return re.sub(r"^((?:[A-Za-z]+/)?)Spec/", r"\1Proof/", spec, count=1).replace(
        "TopLevelRobustness.lean", "TopLevelWitness.lean")


def strip_comments(src: str) -> str:
    src = re.sub(r"/-.*?-/", "", src, flags=re.S)
    return re.sub(r"--[^\n]*", "", src)


def current() -> dict[str, set[str] | None]:
    """Each statement (`<spec file>:<X>`): the binders its witness leaves out, or None if it has
    none."""
    res: dict[str, set[str] | None] = {}
    for spec in spec_files():
        names = SPEC_DEF.findall(strip_comments((ROOT / spec).read_text()))
        wf = ROOT / witness_file(spec)
        wits: dict[str, set[str]] = {}
        if wf.exists():
            for m in WITNESS.finditer(strip_comments(wf.read_text())):
                if m.group(1) != m.group(2):
                    print(f"premise-witness: {wf.relative_to(ROOT)}: {m.group(1)}.premisesSat "
                          f"is about {m.group(2)}.spec", file=sys.stderr)
                    continue
                wits[m.group(1)] = {b.strip() for b in (m.group(3) or "").split(",") if b.strip()}
        for x in names:
            res[f"{spec}:{x}"] = wits.get(x)
    return res


def read_baseline() -> list[tuple[str, str, str, str]]:
    rows = []
    if not BASELINE.exists():
        return rows
    for ln, line in enumerate(BASELINE.read_text().splitlines(), 1):
        if not line.strip() or line.startswith("#"):
            continue
        parts = line.split(None, 3)
        if len(parts) < 4 or parts[2] not in CLASSES:
            sys.exit(f"premise-witness: {BASELINE.name}:{ln}: expected "
                     f"'<statement> <binder|*> <class> <reason>', class in {sorted(CLASSES)}")
        rows.append((parts[0], parts[1], parts[2], parts[3]))
    return rows


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--update", action="store_true", help="with --check: drop stale baseline lines")
    ap.add_argument("--list", action="store_true")
    a = ap.parse_args()
    cur = current()
    base = read_baseline()
    listed = {(s, b) for s, b, _, _ in base}
    errors, stale = [], []
    for st, dropped in cur.items():
        if dropped is None:
            if (st, "*") not in listed:
                errors.append(f"{st}: no witness ({witness_file(st.split(':')[0])}), and not in the baseline")
            continue
        for b in sorted(dropped):
            if (st, b) not in listed:
                errors.append(f"{st}: its witness leaves out {b}, which the baseline does not list")
    for row in base:
        s, b = row[0], row[1]
        d = cur.get(s, "gone")
        if d == "gone" or (b == "*" and d is not None) or (b != "*" and (d is None or b not in d)):
            stale.append(row)
    if a.list:
        for st, d in cur.items():
            print(f"{st}: " + ("no witness" if d is None else
                              ("witnessed" + (f", leaving out {', '.join(sorted(d))}" if d else ""))))
    if a.check and a.update and stale:
        keep = [r for r in base if r not in stale]
        head = [l for l in BASELINE.read_text().splitlines() if l.startswith("#")]
        BASELINE.write_text("\n".join(head + [" ".join(r) for r in keep]) + "\n")
        print(f"premise-witness: dropped {len(stale)} stale baseline lines")
        stale = []
    for e in errors:
        print(f"premise-witness: {e}")
    for r in stale:
        print(f"premise-witness: baseline line no longer needed (--check --update): {' '.join(r[:3])}")
    n_wit = sum(1 for d in cur.values() if d is not None)
    full = sum(1 for d in cur.values() if d == set())
    if errors or stale:
        print(f"premise-witness: FAILED ({len(errors)} unlisted, {len(stale)} stale)")
        return 1
    print(f"premise-witness: ok ({len(cur)} statements, {n_wit} witnessed, {full} with nothing "
          f"left out but Iris contracts, {len(base)} baseline lines)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
