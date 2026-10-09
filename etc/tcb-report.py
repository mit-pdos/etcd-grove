#!/usr/bin/env python3
"""Report the trusted computing base (TCB) of this repository's proofs.

usage: etc/tcb-report.py [-o REPORT.md] [--defs] [--json TCB.json] [--reuse]
                         [--check [--update]]
       etc/tcb-report.py (--roots PATTERN... | --collection FILE) [--per-root]
                         [--check [--update]] [-o OUT] [--json TCB.json] [--reuse]

  -o       where to write the Markdown report (default: stdout)
  --defs   also list every definition the results' statements rest on
  --json   where to keep the raw output of etc/tcb-report.lean (default
           .lake/tcb.json); --reuse skips re-running Lean if it is of the current
           root modules (etc/proof_roots.py)
  --check  compare the project's axioms and sorries with etc/tcb-baseline.txt and
           exit 1 if they differ (`--check --update` rewrites the baseline): a gate
           for CI, where the report is a viewer

  --roots  only the roots matching one of the regular expressions, searched in the
           root's name (`T.wp_M`, without the namespace of the `Link.lean` files), its
           module's file (`Proof/<pkg>/Link.lean`) and its spec's file
           (`Spec/<pkg>/T__M.lean`): print this repository's
           axioms and the `sorry`s they rest on, how many of them reach each, and the
           roots that reach a `sorry` (--per-root: every root)
  --collection  the same for the `roots PATTERN` lines of FILE (one per line, as
           `etc/tcb-collections/*.txt`), whose `axiom X`/`sorry X` lines are its
           baseline: with --check, compared (exit 1 if they differ); with
           --check --update, rewritten (the other lines kept)

Needs a built project (`lake build`).  For a Goose verification project laid out as
CLAUDE.md describes (`Spec/<pkg>/`, `Proof/<pkg>/` with a `Link.lean` per package, the
projects and parts of `etc/goose.py`; etc/proof_roots.py); nothing in it names a
project.  The TCB is read off the elaborated environment, not the source text, so
nothing is a lower bound:

  * assumed -- the axioms the results' proofs depend on and the declarations
    containing a `sorry` (what `#print axioms` shows, with the `sorry`s located);
  * results -- the statements of what the proof exports: the linked result of a Go
    function that no other proof uses (every theorem of a package's
    `Proof/<pkg>/Link.lean` is one function's spec instantiated with its callees'
    results; a spec some other proof uses is internal: were it wrong, that proof would
    fail), and the theorems of each `Results.lean` (results restated or derived);
  * definitions -- this repository's definitions those statements are written in
    terms of, transitively through their bodies.  A wrong definition makes a true
    theorem say nothing, so these are trusted exactly as the axioms are.

Perennial (the framework, the Goose translation, Go's semantics) and Lean are trusted
as a whole and only named.
"""

import argparse
import collections
import json
import os
import re
import subprocess
import sys

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
LEAN_AX = ["propext", "Classical.choice", "Quot.sound"]
BASELINE = os.path.join(ROOT, "etc", "tcb-baseline.txt")

# Where a linked result's statement lives: `Link.lean` states `T.wp_M : T.M.spec`.
SPEC_DIR = "Spec"

sys.dont_write_bytecode = True  # no etc/__pycache__
sys.path.insert(0, os.path.join(ROOT, "etc"))
import proof_roots  # noqa: E402  (etc/proof_roots.py: the root modules, running Lean)

# The namespace of this repository's declarations, not shown.
NS = proof_roots.namespace()
# The modules of linked results (each states `T.wp_M : T.M.spec`): every `Link.lean`
# under `Proof/` (and a part's `<root>/Proof/`).
LINKS = tuple(proof_roots.link_modules())
# This repository's specs and proofs: `Spec/`, `Proof/`, and the parts'.
PROJECT_DIRS = proof_roots.PROJECT_DIRS
PROJECT_MODS = proof_roots.PROJECT_MODS

# Source constructs that weaken what the kernel checks.
RISKY = [
    (r"\bnative_decide\b", "`native_decide` (trusts the compiler)"),
    (r"@\[\s*implemented_by", "`implemented_by`"),
    (r"@\[\s*extern", "`extern`"),
    (r"\bunsafe\b", "`unsafe`"),
    (r"debug\.skipKernelTC", "`debug.skipKernelTC`"),
    (r"^\s*opaque\b", "`opaque`"),
    (r"\bOfReduceBool\b|\bLean\.ofReduceBool\b", "`ofReduceBool`"),
]


def short(n):
    # a private name is `_private.<module>.0.<name>`
    m = re.match(r"_private\.(?:[^.]+\.)*?0\.(.*)$", n)
    if m:
        n = m.group(1)
    return n.removeprefix(NS)


def read(path):
    with open(path, encoding="utf-8") as f:
        return f.read()


def mod_path(m):
    return m.replace(".", "/") + ".lean"


def loc(o):
    return f"`{mod_path(o['module'])}:{o['line']}`"


def first_para(doc):
    doc = doc.strip()
    if not doc:
        return ""
    para = re.split(r"\n\s*\n", doc)[0]
    return " ".join(para.split())


def spec_file(root, defs):
    """The Spec file of a linked result: the module of the `….spec` it states."""
    for d in root["defs"]:
        if d.endswith(".spec") and d in defs:
            return mod_path(defs[d]["module"])
    return mod_path(root["module"])


def git(*args):
    try:
        return subprocess.run(
            ["git", *args], cwd=ROOT, capture_output=True, text=True, check=False
        ).stdout.strip()
    except OSError:
        return ""


def scan_sources():
    hits = []
    for dp, _, fs in (w for d in PROJECT_DIRS for w in os.walk(os.path.join(ROOT, d))):
        for f in fs:
            if not f.endswith(".lean"):
                continue
            p = os.path.join(dp, f)
            in_comment = 0
            for i, line in enumerate(read(p).splitlines(), 1):
                code = line
                # drop block and line comments (good enough for these keywords)
                out = ""
                j = 0
                while j < len(code):
                    if in_comment:
                        k = code.find("-/", j)
                        if k < 0:
                            j = len(code)
                        else:
                            in_comment -= 1
                            j = k + 2
                    elif code.startswith("/-", j):
                        in_comment += 1
                        j += 2
                    elif code.startswith("--", j):
                        break
                    else:
                        out += code[j]
                        j += 1
                for pat, what in RISKY:
                    if re.search(pat, out):
                        hits.append((what, os.path.relpath(p, ROOT), i))
    return hits


def matches(r, pat, defs):
    """Whether root `r` is selected by the regular expression `pat`: searched in its
    name (`T.wp_M`), its module's file and, for a linked result, its spec's file
    (`Spec/<pkg>/T__M.lean`)."""
    keys = [short(r["name"]), mod_path(r["module"])]
    if r["module"] in LINKS:
        keys.append(spec_file(r, defs))
    return any(re.search(pat, k) for k in keys)


def check(path, current, kept, srs, sorries, update):
    """Compare the `axiom X`/`sorry X` entries `current` with those of the file `path`
    (exit status 1 if they differ, or if a `sorry` of `srs` is an elaboration error);
    `update` rewrites its entries, keeping the lines `kept` (comments, `roots` lines)."""
    rel = proof_roots.shown(path)
    if update:
        with open(path, "w") as f:
            f.write("".join(x + "\n" for x in kept + current))
        print(f"tcb: wrote {rel} ({len(current)} entries)")
        return 0
    base = [x.strip() for x in read(path).splitlines() if x.startswith(("axiom ", "sorry "))]
    added = sorted(set(current) - set(base))
    removed = sorted(set(base) - set(current))
    synth = [n for n in srs if sorries[n]["synthetic"]]
    for a in added:
        print(f"tcb: NEW in the trust base: {a}")
    for a in removed:
        print(f"tcb: gone from the trust base (update {rel}): {a}")
    for x in synth:
        print(f"tcb: elaboration error (synthetic sorry) in {short(x)}")
    if added or removed or synth:
        return 1
    n_ax = sum(1 for x in current if x.startswith("axiom "))
    print(f"tcb: trust base matches {rel} ({n_ax} axioms, {len(current) - n_ax} sorries)")
    return 0


def selection_report(sel, pats, n_roots, sel_ax, sel_sr, axioms, sorries, users, fw_ax,
                     defs, per_root):
    """What the roots `sel` rest on, in plain text."""
    names = {r["name"] for r in sel}
    out = []
    w = out.append
    w(f"{len(sel)} of {n_roots} roots match {' '.join(repr(p) for p in pats)}.")
    clean = [r for r in sel if not r["sorries"]]
    w(f"{len(clean)} of them reach no `sorry`.")
    w("")
    w(f"This repository's axioms they rest on: {len(sel_ax)}")
    rows = [(short(n), loc(axioms[n]).strip("`"), len(names & set(users[n]))) for n in sel_ax]
    rows += [] if rows else [("(none)", "", 0)]
    wa = max(len(x[0]) for x in rows)
    wb = max(len(x[1]) for x in rows)
    for a, l, k in rows:
        w(f"  {a.ljust(wa)}  {l.ljust(wb)}  {f'reached by {k}' if l else ''}".rstrip())
    w("")
    w(f"Unfinished proofs (`sorry`) they reach: {len(sel_sr)}")
    rows = [(short(n), loc(sorries[n]).strip("`")
             + (" (elaboration error)" if sorries[n]["synthetic"] else ""),
             len(names & set(users[n]))) for n in sel_sr]
    rows += [] if rows else [("(none)", "", 0)]
    wa = max(len(x[0]) for x in rows)
    wb = max(len(x[1]) for x in rows)
    for a, l, k in rows:
        w(f"  {a.ljust(wa)}  {l.ljust(wb)}  {f'reached by {k}' if l else ''}".rstrip())
    w("")
    n_fw = len({a for r in sel for a in r["axioms"] if a in fw_ax})
    w(f"Perennial's axioms (Go types Goose does not translate): {n_fw}.")
    w("")
    listed = sel if per_root else [r for r in sel if r["sorries"]]
    if listed:
        w(("Every root" if per_root else "The roots that reach a `sorry` (--per-root: every root)")
          + ":")
        wa = max([len(short(r["name"])) for r in listed] + [4])
        w(f"  {'root'.ljust(wa)}  sorry  axioms  statement")
        for r in listed:
            pa = sum(1 for a in r["axioms"] if a in sel_ax)
            where = spec_file(r, defs) if r["module"] in LINKS else mod_path(r["module"])
            w(f"  {short(r['name']).ljust(wa)}  {len(r['sorries']):5}  {pa:6}  {where}")
        w("")
    return "\n".join(out)


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("-o", "--out")
    ap.add_argument("--defs", action="store_true")
    ap.add_argument("--json", default=os.path.join(ROOT, ".lake", "tcb.json"))
    ap.add_argument("--reuse", action="store_true")
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--update", action="store_true")
    ap.add_argument("--roots", nargs="+", metavar="PATTERN")
    ap.add_argument("--collection", metavar="FILE")
    ap.add_argument("--per-root", action="store_true")
    args = ap.parse_args()

    roots, axioms, sorries, defs = {}, {}, {}, {}
    for o in proof_roots.load(args.json, "tcb", args.reuse):
        {"root": roots, "axiom": axioms, "sorry": sorries, "def": defs}[o["t"]][
            o["name"]
        ] = o
    used = {u for r in roots.values() for u in r["uses"]}
    exported = sorted(
        (r for n, r in roots.items() if n not in used),
        key=lambda r: (r["module"] not in LINKS, r["module"], short(r["name"])),
    )
    trusted_defs = sorted({d for r in exported for d in r["defs"] if d in defs})

    def nlines(d):
        return defs[d]["endLine"] - defs[d]["line"] + 1

    def is_project(n):
        return n in axioms and axioms[n]["module"].startswith(PROJECT_MODS)

    proj_ax = sorted(n for n in axioms if is_project(n))
    lean_ax = [n for n in LEAN_AX if n in axioms]
    fw_ax = sorted(
        n for n in axioms if not is_project(n) and n not in LEAN_AX and n != "sorryAx"
    )

    users = collections.defaultdict(list)  # axiom/sorry -> roots depending on it
    for r in roots.values():
        for a in r["axioms"]:
            users[a].append(r["name"])
        for s in r["sorries"]:
            users[s].append(r["name"])

    def entries(axs, srs):
        return sorted([f"axiom {short(n)}" for n in axs] + [f"sorry {short(n)}" for n in srs])

    # --roots/--collection: what a collection of roots rests on
    if args.collection:
        coll = read(args.collection).splitlines()
        pats = [x.split(None, 1)[1].strip() for x in coll if x.startswith("roots ")]
        if args.roots:
            sys.exit("tcb: give --roots or --collection, not both")
        if not pats:
            sys.exit(f"tcb: {args.collection} has no `roots PATTERN` line")
    else:
        pats = args.roots or []
    if pats:
        sel = []
        for p in pats:
            hit = [r for r in roots.values() if matches(r, p, defs)]
            if not hit:
                sys.exit(f"tcb: no root matches {p!r}")
            sel += [r for r in hit if r not in sel]
        sel.sort(key=lambda r: short(r["name"]))
        sel_ax = sorted({a for r in sel for a in r["axioms"] if is_project(a)})
        sel_sr = sorted({x for r in sel for x in r["sorries"]})
        current = entries(sel_ax, sel_sr)
        if args.check:
            kept = [x for x in coll if not x.startswith(("axiom ", "sorry "))]
            return check(args.collection, current, kept, sel_sr, sorries, args.update)
        text = selection_report(sel, pats, len(roots), sel_ax, sel_sr, axioms, sorries,
                                users, fw_ax, defs, args.per_root)
        if args.out:
            with open(args.out, "w") as f:
                f.write(text)
            print(f"tcb: wrote {args.out}", file=sys.stderr)
        else:
            print(text, end="")
        return 0

    # --check: the project's part of the trust base against the baseline
    if args.check:
        kept = ["# This repository's part of the proofs' trust base "
                "(etc/tcb-report.py --check --update)."]
        return check(BASELINE, entries(proj_ax, sorries), kept, sorries, sorries,
                     args.update)

    out = []
    w = out.append
    head = git("rev-parse", "--short", "HEAD")
    dirty = (
        " (with uncommitted changes)"
        if git("status", "--porcelain", "--", *PROJECT_DIRS)
        else ""
    )
    man = json.loads(read(os.path.join(ROOT, "lake-manifest.json")))
    pin = next((p["rev"][:9] for p in man["packages"] if p["name"] == "perennial"), "?")
    toolchain = read(os.path.join(ROOT, "lean-toolchain")).strip()

    w("# Trusted computing base\n")
    w(
        f"Generated by `etc/tcb-report.py` at `{head}`{dirty}; Perennial `{pin}`, `{toolchain}`. "
        "Do not edit by hand.\n"
    )
    w(
        f"Roots: the {len(roots)} theorems of "
        + ", ".join(f"`{mod_path(m)}`" for m in proof_roots.root_modules())
        + " (each `Link.lean` holds a package's linked results: every Go function's spec "
        "instantiated with its callees' results; each `Results.lean` its exported results).\n"
    )

    w("## Summary\n")
    n_sorry = sum(1 for r in roots.values() if r["sorries"])
    w(
        f"- Unfinished proofs (`sorry`): **{len(sorries)}**, reached by {n_sorry} of "
        f"{len(roots)} roots."
    )
    w(f"- This repository's axioms (trust boundary): **{len(proj_ax)}**.")
    w(f"- Perennial's axioms (Go types Goose does not translate): {len(fw_ax)}.")
    w(f"- Lean's axioms: {', '.join(f'`{a}`' for a in lean_ax)}.")
    w(
        f"- Results (exported statements): **{len(exported)}**, written in terms of "
        f"**{len(trusted_defs)}** of this repository's definitions "
        f"(~{sum(nlines(d) for d in trusted_defs)} lines). The other "
        f"{len(roots) - len(exported)} linked results are internal."
    )
    risky = scan_sources()
    w(
        f"- Constructs that bypass or weaken kernel checking in `Spec/` and `Proof/`: "
        f"{len(risky) if risky else 'none'}.\n"
    )

    w("## Results\n")
    w(
        "What the proof exports: the linked results no other proof uses, and the "
        "protocol lemmas of `Results.lean`. Reading these statements, and the "
        "definitions below, is what believing the proof takes.\n"
    )
    w(
        "| result | statement | `sorry` | this repo's axioms | Perennial axioms | definitions |"
    )
    w("|---|---|---|---:|---:|---:|")
    for r in exported:
        sr = ", ".join(f"`{short(x)}`" for x in r["sorries"]) or "none"
        pa = sum(1 for a in r["axioms"] if is_project(a))
        fa = sum(1 for a in r["axioms"] if a in fw_ax)
        where = (
            f"`{spec_file(r, defs)}`"
            if r["module"] in LINKS
            else f"`{mod_path(r['module'])}:{r['line']}`"
        )
        w(f"| `{short(r['name'])}` | {where} | {sr} | {pa} | {fa} | {len(r['defs'])} |")
    clean = sum(
        1
        for r in roots.values()
        if not r["sorries"]
        and not any(is_project(a) or a in fw_ax for a in r["axioms"])
    )
    w(
        f"\nOf all {len(roots)} roots (internal ones included), {clean} depend on Lean's "
        f"axioms only, and {len(roots) - n_sorry} on no `sorry`.\n"
    )

    w("## Definitions the results rest on\n")
    w(
        "This repository's definitions the exported statements are written in terms of, "
        "transitively (through definition bodies, not proofs), by file. "
        "`--defs` lists them.\n"
    )
    by_file = collections.defaultdict(list)
    for d in trusted_defs:
        by_file[mod_path(defs[d]["module"])].append(d)
    w("| file | definitions | lines |")
    w("|---|---:|---:|")
    for f in sorted(by_file, key=lambda f: -sum(nlines(d) for d in by_file[f])):
        w(f"| `{f}` | {len(by_file[f])} | {sum(nlines(d) for d in by_file[f])} |")
    w("")
    if args.defs:
        for f in sorted(by_file):
            w(
                f"- `{f}`: "
                + ", ".join(f"`{short(d)}` ({defs[d]['line']})" for d in by_file[f])
            )
        w("")

    w("## Unfinished proofs\n")
    if not sorries:
        w("None.\n")
    for n, o in sorted(sorries.items()):
        kind = " (**elaboration error**)" if o["synthetic"] else ""
        w(
            f"- `{short(n)}`{kind}, {loc(o)}: reached by {len(users[n])} roots, "
            f"including {', '.join(f'`{short(u)}`' for u in sorted(users[n])[:6])}"
            f"{', …' if len(users[n]) > 6 else ''}."
        )
    w("")

    w("## This repository's axioms\n")
    w(
        "The trust boundary: abstract predicates for state the proof does not model, and "
        "the specs of Go functions outside the proof's scope (each mirrors a Rocq `Axiom`). "
        "Each must be justified by its doc comment.\n"
    )
    w("| axiom | where | used by | why (doc comment) |")
    w("|---|---|---:|---|")
    for n in proj_ax:
        o = axioms[n]
        doc = first_para(o["doc"]).replace("|", "\\|") or "(no doc comment)"
        if len(doc) > 300:
            doc = doc[:297] + "…"
        w(f"| `{short(n)}` | {loc(o)} | {len(users[n])} | {doc} |")
    w("")

    w("## Perennial's axioms\n")
    w(
        "Goose declares, without translating them, the Go types its translation mentions "
        "but does not model (`T`, `T.underlying`, `T.zero_val`). They are reached through "
        "the translated package's declarations, not used by a proof step.\n"
    )
    by_mod = collections.defaultdict(list)
    for n in fw_ax:
        by_mod[axioms[n]["module"]].append(n)
    w("| module | axioms |")
    w("|---|---|")
    for m in sorted(by_mod):
        w(f"| `{m}` | {', '.join(f'`{a}`' for a in by_mod[m])} |")
    w("")

    w("## Not checked by Lean\n")
    w(
        f"- **Lean** (`{toolchain}`): the kernel, and the elaborator only in that a "
        "`theorem`'s *statement* is what it elaborates to."
    )
    w(
        f"- **Perennial** (`{pin}`): the Goose translations (`Code/`"
        + "".join(f", `{r}/Code/`" for r in proof_roots.PART_ROOTS)
        + ") are trusted to mean what the Go code means, and Perennial's Go semantics "
        "to be Go's."
    )
    w(
        "- **The statements**: a proved theorem says only what its statement says. The "
        "results and the definitions they rest on, listed above, are what must be read."
    )
    if risky:
        w("- **Constructs that weaken kernel checking** in `Spec/` and `Proof/`:")
        for what, p, i in risky:
            w(f"  - {what} at `{p}:{i}`")
    w("")

    text = "\n".join(out)
    if args.out:
        with open(args.out, "w") as f:
            f.write(text)
        print(f"tcb: wrote {args.out}", file=sys.stderr)
    else:
        print(text)
    return 0


if __name__ == "__main__":
    sys.exit(main())
