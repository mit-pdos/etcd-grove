#!/usr/bin/env python3
"""Write a top-level theorem's trusted computing base (TCB) out as a directory of Lean to read.

usage: etc/theorem-tcb.py THEOREM... [-o DIR] [--collection FILE] [--file PATH] [--no-comments]

For each theorem, `DIR/<theorem>/` (default: a fresh temporary directory, printed) holds

  README.md   what is in it, what is not, and the line counts by part and by file;
  TCB.lean    every trusted declaration in reading order: the theorem's statement, then
              (1) the premises -- what the statement is written in terms of, (2) the axioms
              its proof rests on, (3) the definitions reached only through those axioms;
  <tree>/     the same declarations in a copy of this repository's layout, each file trimmed
              to its trusted declarations (in source order), for reading them next to their
              neighbours.

The declarations are exactly those etc/theorem-loc.py counts (see its --help: what the TCB is,
which `etc/tcb-collections` file gives the axioms, what a source-level reading does not follow).
Each is copied verbatim (with its doc comment, unless --no-comments) under the `namespace`s,
`open`s and `variable`s it was declared in, and tagged with its part.  The output is for
reading, not for building: names of Perennial, Iris, Lean and Goose's translation (`Code/`,
`GeneratedProof/`) are left as they are -- they are trusted as a whole and not included.
"""

import argparse
import collections
import importlib.util
import os
import re
import sys
import tempfile

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
_spec = importlib.util.spec_from_file_location("theorem_loc", os.path.join(ROOT, "etc", "theorem-loc.py"))
TL = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(TL)

PARTS = [("stmt", "Premises", "what the theorem's statement is written in terms of"),
         ("axiom", "Axioms", "the axioms the theorem's proof rests on"),
         ("axvocab", "Axiom vocabulary", "definitions reached only through the axioms")]
TAG = {"stmt": "premise", "axiom": "axiom", "axvocab": "axiom vocabulary"}


def raw_lines(path, cache={}):
    if path not in cache:
        with open(path, encoding="utf-8") as f:
            cache[path] = f.read().split("\n")
    return cache[path]


def decl_text(d, comments):
    """A declaration's source lines: verbatim, or without comments (blank lines dropped)."""
    if comments:
        return "\n".join(raw_lines(d.file)[d.start:d.end + 1])
    code = TL.stripped_lines(d.file)[d.start:d.end + 1]
    return "\n".join(l.rstrip() for l in code if l.strip())


def statement_text(root, comments):
    """The theorem's declaration up to its `:=` (the proof is not trusted)."""
    lines = raw_lines(root.file)[root.start:root.end + 1] if comments else \
        [l for l in TL.stripped_lines(root.file)[root.start:root.end + 1]]
    text = "\n".join(lines)
    # cut at the statement's `:=`, found on the comment-free text (same offsets)
    code = "\n".join(TL.stripped_lines(root.file)[root.start:root.end + 1])
    kw = re.search(r"\b(theorem|lemma)\b", code)
    stmt = TL.statement_of(code[kw.start():])
    return text[:kw.start() + len(stmt)].rstrip() + " := by\n  -- (the proof: not part of the TCB)\n  sorry"


def by_axiom(env, root, decls):
    """The axioms in file order, each with the axiom-vocabulary definitions it is the first to
    reach (one walk per axiom, sharing what the statement and earlier axioms reached)."""
    vocab = {id(d) for d in decls if d.cat == "axvocab"}
    seen = {id(root)} | {id(d) for d in decls if d.cat == "stmt"}
    axioms = sorted((d for d in decls if d.cat == "axiom"), key=lambda d: (d.file, d.start))
    seen |= {id(a) for a in axioms}
    groups = []
    for a in axioms:
        got = []

        def visit(t):
            if t.kind in TL.PROOF_KINDS:
                return False
            if id(t) in vocab:
                got.append(t)
            return True
        env.walk([(a, a.code + "\n" + "\n".join(a.vars))], seen, visit)
        groups.append((a, sorted(got, key=lambda d: (d.file, d.start))))
    return groups


def context_key(d):
    return (tuple(d.ns), tuple(d.opens), tuple(d.vars))


def emit_block(out, decls, comments, tag=True):
    """Write `decls` (in order) with their scopes: a block per run of declarations sharing
    namespace, `open`s and `variable`s."""
    for (ns, opens, vars_), group in _runs(decls):
        out.append("")
        for n in ns:
            out.append(f"namespace {n}")
        out.append("section")
        if opens:
            out.append("open " + " ".join(dict.fromkeys(opens)))
        for v in vars_:
            out.append(v.strip())
        for d in group:
            out.append("")
            if tag:
                rel = os.path.relpath(d.file, ROOT)
                out.append(f"-- [{TAG[d.cat]}] {rel}:{d.start + 1}-{d.end + 1} "
                           f"({TL.code_lines(d)} code lines)")
            out.append(decl_text(d, comments))
        out.append("")
        out.append("end")
        for n in reversed(ns):
            out.append(f"end {n}")


def _runs(decls):
    runs = []
    for d in decls:
        k = context_key(d)
        if runs and runs[-1][0] == k:
            runs[-1][1].append(d)
        else:
            runs.append((k, [d]))
    return runs


def write_theorem(name, args, outdir):
    file = TL.find_theorem(name, args.file)
    rel = os.path.relpath(file, ROOT)
    coll = args.collection or TL.find_collection(rel, name)
    env = TL.Env(file)
    root = next((d for d in env.decls if d.file == file and d.name
                 and d.name.split(".")[-1] == name and d.kind in ("theorem", "lemma")), None)
    if root is None:
        sys.exit(f"theorem-tcb: {name} not found in {rel}")
    for d in env.decls:
        d.cat = None
    decls, missing = TL.tcb(env, root, coll)
    tdir = os.path.join(outdir, name)
    os.makedirs(tdir, exist_ok=True)
    comments = not args.no_comments

    # TCB.lean, in reading order
    out = [f"/-! # The trusted computing base of `{name}`",
           "",
           f"Generated by `etc/theorem-tcb.py` from `{rel}`"
           + (f" with the axioms of `{os.path.relpath(coll, ROOT)}`." if coll else " (no axiom collection)."),
           "For reading, not building; see README.md. -/", "",
           "/-! ## The theorem's statement -/", ""]
    for n in root.ns:
        out.append(f"namespace {n}")
    out.append("section")
    if root.opens:
        out.append("open " + " ".join(dict.fromkeys(root.opens)))
    out += [v.strip() for v in root.vars]
    out += ["", statement_text(root, comments), "", "end"] + [f"end {n}" for n in reversed(root.ns)]
    totals = {}
    for cat, title, what in PARTS:
        ds = [d for d in decls if d.cat == cat]
        totals[cat] = (len(ds), sum(TL.code_lines(d) for d in ds))
    stmt = sorted((d for d in decls if d.cat == "stmt"), key=lambda d: (d.file, d.start))
    out += ["", "", f"/-! ## Premises: {PARTS[0][2]} ({totals['stmt'][0]} declarations, "
            f"{totals['stmt'][1]} code lines) -/"]
    emit_block(out, stmt, comments)
    out += ["", "", f"/-! ## Axioms ({totals['axiom'][0]} declarations, {totals['axiom'][1]} code "
            f"lines) and their vocabulary ({totals['axvocab'][0]} declarations, "
            f"{totals['axvocab'][1]} code lines)", "",
            "Each axiom is followed by the definitions it is the first (in file order) to reach:",
            "its spec, and what that spec is written in. A definition an earlier axiom (or the",
            "statement) already reached is not repeated. -/"]
    for a, vocab in by_axiom(env, root, decls):
        out += ["", f"/-! ### `{a.name.removeprefix(TL.proof_roots.namespace())}` "
                f"({TL.code_lines(a) + sum(TL.code_lines(d) for d in vocab)} code lines with "
                f"{len(vocab)} definitions) -/"]
        emit_block(out, [a] + vocab, comments)
    with open(os.path.join(tdir, "TCB.lean"), "w", encoding="utf-8") as f:
        f.write("\n".join(out) + "\n")

    # the trimmed tree
    byfile = collections.defaultdict(list)
    for d in decls:
        byfile[d.file].append(d)
    byfile[root.file].append(root)
    filerows = []
    for path, ds in sorted(byfile.items()):
        ds.sort(key=lambda d: d.start)
        frel = os.path.relpath(path, ROOT)
        lines = [f"/-! Trimmed by `etc/theorem-tcb.py` to the declarations of `{frel}` in the TCB "
                 f"of `{name}`. -/"]
        trusted = [d for d in ds if d is not root]
        for (ns, opens, vars_), group in _runs(ds):
            lines.append("")
            lines += [f"namespace {n}" for n in ns] + ["section"]
            if opens:
                lines.append("open " + " ".join(dict.fromkeys(opens)))
            lines += [v.strip() for v in vars_]
            for d in group:
                lines.append("")
                if d is root:
                    lines += ["-- [the theorem's statement]", statement_text(root, comments)]
                else:
                    lines += [f"-- [{TAG[d.cat]}] line {d.start + 1}", decl_text(d, comments)]
            lines += ["", "end"] + [f"end {n}" for n in reversed(ns)]
        dest = os.path.join(tdir, "tree", frel)
        os.makedirs(os.path.dirname(dest), exist_ok=True)
        with open(dest, "w", encoding="utf-8") as f:
            f.write("\n".join(lines) + "\n")
        if trusted:
            filerows.append((sum(TL.code_lines(d) for d in trusted), len(trusted), frel,
                             collections.Counter(TAG[d.cat] for d in trusted)))

    # README.md
    total = sum(n for _, n in totals.values())
    r = [f"# TCB of `{name}`", "",
         f"Theorem: `{root.name}` (`{rel}:{root.start + 1}`).",
         f"Axioms: `{os.path.relpath(coll, ROOT)}` (its baseline's `axiom` lines)." if coll else
         "Axioms: no `etc/tcb-collections` file matches; none included.", "",
         f"**{total} code lines** (non-blank, non-comment) in {sum(c for c, _ in totals.values())} "
         "declarations of this repository's `Spec/` and `Proof/`:", "",
         "| part | declarations | code lines |", "|---|---:|---:|"]
    for cat, title, what in PARTS:
        r.append(f"| {title} ({what}) | {totals[cat][0]} | {totals[cat][1]} |")
    r += ["",
          "Read `TCB.lean` top to bottom: the statement, then what it is written in, then the axioms",
          "and what they are written in. `tree/` has the same declarations in their files.", "",
          "Not included, trusted as a whole: Lean, Iris, Perennial (Go's semantics, the framework),",
          "and Goose's translation of the Go code (`Code/`, `GeneratedProof/`); the names of these",
          "are left unresolved. The proofs are not part of the TCB and are left out.", "",
          "This is a reading of the source text (`etc/theorem-loc.py --help`): instances found by",
          "typeclass resolution, coercions and notation are not followed, and a name that several",
          "`open`s could mean includes every candidate.", ""]
    if missing:
        r += [f"**{len(missing)} axioms of the collection were not found in the source** "
              "(a stale baseline?): " + ", ".join(f"`{m}`" for m in missing), ""]
    r += ["## By file", "", "| code lines | declarations | parts | file |", "|---:|---:|---|---|"]
    for n, k, frel, parts in sorted(filerows, key=lambda x: (-x[0], x[2])):
        r.append(f"| {n} | {k} | {', '.join(f'{c} {p}' for p, c in sorted(parts.items()))} | "
                 f"`tree/{frel}` |")
    with open(os.path.join(tdir, "README.md"), "w", encoding="utf-8") as f:
        f.write("\n".join(r) + "\n")
    return tdir, total, totals


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0],
                                 formatter_class=argparse.RawDescriptionHelpFormatter, epilog=__doc__)
    ap.add_argument("theorems", nargs="+")
    ap.add_argument("-o", "--out")
    ap.add_argument("--collection")
    ap.add_argument("--file")
    ap.add_argument("--no-comments", action="store_true")
    args = ap.parse_args()
    outdir = os.path.abspath(args.out) if args.out else tempfile.mkdtemp(prefix="tcb-")
    os.makedirs(outdir, exist_ok=True)
    for name in args.theorems:
        tdir, total, totals = write_theorem(name, args, outdir)
        print(f"{name}: {total} code lines (premises {totals['stmt'][1]}, axioms {totals['axiom'][1]}, "
              f"axiom vocabulary {totals['axvocab'][1]}) -> {tdir}")
    print(outdir)


if __name__ == "__main__":
    main()
