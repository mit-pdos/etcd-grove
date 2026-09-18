#!/usr/bin/env python3
"""Show what a Rocq development leaves unproven, and how big its TCB is.

Two questions this answers, which are otherwise answered by grepping and
counting by hand:

  1. **Where is the proof incomplete?**  A file-by-file status --
     ``admitted``, ``assumed``, ``proved``, ``stated``, ``defs``,
     ``plumbing`` -- and, for the files that carry debt, which declarations
     carry it.

  2. **How big is the trusted computing base?**  Not "how many axioms", which
     misses the larger half: a theorem is only as good as the definitions its
     statement is written in terms of.

What counts as the TCB here, and why:

  * **assumed** -- every ``Axiom``/``Parameter``/``Conjecture``/
    ``Hypothesis`` that is not inside a ``Module Type``, and every proof that
    ends in ``Admitted``.  Believed without proof, so believed.
  * **results** -- the statements of the things the development exports: a
    Hoare triple for a Go function that nothing else in the development
    calls, and a theorem in a file that nothing else requires.  A reader has
    to read these to know what was proved.
  * **definitions** -- everything those statements are written in terms of,
    transitively.  The abstract state machine, the ghost-state predicates,
    the refinement relation.  A wrong definition here makes a true theorem
    say nothing, so this is trusted in exactly the sense the axioms are, and
    it is usually the biggest part.

And what does *not* count, which is the other half of the point:

  * **obligations** -- a ``Parameter`` inside a ``Module Type``.  The functor
    ascribed to that signature discharges it, so it reaches no ``Print
    Assumptions``.  In a development that states every internal function's
    spec as a signature, this is most of the "axiom-looking" text in the
    tree and none of it is assumed.
  * **internal specs and proofs** -- the spec of a function that something
    else in the development calls is an untrusted proof artifact: if it is
    wrong, the proof that uses it fails.  Proof bodies likewise.  Both are
    measured, so you can see how much is *not* being trusted.

Usage::

    etc/tcb-report.py                        # summary + what is incomplete
    etc/tcb-report.py --scope election       # one directory of it
    etc/tcb-report.py --view files           # every file's status
    etc/tcb-report.py --view assumed         # every axiom and admit
    etc/tcb-report.py --view surface         # the exported statements
    etc/tcb-report.py --view all
    etc/tcb-report.py --format json
    etc/tcb-report.py --selftest

Always exits 0: this is a viewer, not a gate.  ``etc/check-module-discipline.py``
is the gate, and the two share their parser (``etc/rocqscan.py``).

Nothing here knows any particular package, function or file name.  It does
know the *conventions* named in the constants below -- the collection layout,
Perennial's triple notation, Goose's rendering of a call -- so
``--proof-root`` aims it at another development that shares them, and it
degrades to the file-status half for one that does not.

How much to believe it
----------------------
The reference graph is built by matching identifier spellings, so:

  * a reference through a ``Notation`` is invisible, and so is one through a
    typeclass instance found by unification rather than named;
  * a definition from outside the scanned tree -- Perennial, stdpp, Rocq's
    standard library -- is *not* counted.  That framework is trusted too, and
    is a far bigger body of code than anything measured here; the number this
    prints is the development's own TCB on top of it.

Both make the definition count a **lower bound**.  ``--view surface`` prints
how many references it could not resolve, which is the honest way to see how
much is missing.
"""

import argparse
import collections
import json
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import rocqscan  # noqa: E402  (after sys.path is set up)
from rocqscan import (  # noqa: E402
    ASSUMPTION_KINDS,
    PROVABLE_KINDS,
    TYPE_KINDS,
    is_exported,
    iter_files,
    qualified,
    requires,
    scan_file,
    strip_comments,
)

# --------------------------------------------------------------------------
# Defaults and conventions.

# The development to look at.  Any tree of .v files will do.
DEFAULT_PROOF_ROOT = "new/proof/go_etcd_io/raft"

# The file kinds of a spec/postulates/proof/link collection, as
# etc/check-module-discipline.py defines them.  Used for two things: to tell
# an internal function's spec from an exported one (a collection nothing else
# requires is a root of the call graph), and to keep a collection's four
# files from being counted as four separate specifications.
ROLES = ("spec", "postulates", "proof", "link")
HELPERS_SUFFIX = "_helpers"
ROLE_RE = re.compile(r"^(?P<role>{})_(?P<x>.+)$".format("|".join(ROLES)))
HELPERS_RE = re.compile(r"^proof_(?P<x>.+){}$".format(re.escape(HELPERS_SUFFIX)))

# A spec states its triple as `Definition wp_<fn>_body := ∀ …`; the Module
# Type's Parameter refers to it.  So the `_body` is where the statement's
# text lives, and it is the thing to measure.
BODY_SUFFIX = "_body"

# A deliberate assumption -- one the development means to keep -- says so in
# a comment on the same line.  Everything else is debt.
TRUSTED_MARKER = r"\bTrusted\b"

# An assumption whose statement ends in a sort or in `iProp Σ` declares an
# opaque constant rather than asserting anything: `Axiom own_raft_ghost : ∀ γ
# id s, iProp Σ.` introduces a predicate you cannot see, which is a different
# (and milder) thing to trust than a claim that could be false.
DECLARATION_TAIL_RE = re.compile(
    r"(?:Type|Set|Prop|iProp\s+\S+|iProp)\s*\.?\s*$"
)


# --------------------------------------------------------------------------
# The development

Unit = collections.namedtuple("Unit", "path rel logpath role collection decls lines")


def classify(path):
    """(role, collection) for a file, per the collection layout."""
    base = os.path.basename(path)[:-2]
    hm = HELPERS_RE.match(os.path.basename(os.path.dirname(path)))
    if hm:
        return "helper", hm.group("x")
    m = ROLE_RE.match(base)
    if not m:
        return None, None
    return m.group("role"), m.group("x")


def load(proof_root, root):
    """Scan every .v file under the proof root."""
    units = []
    for path in sorted(iter_files(proof_root)):
        with open(path, encoding="utf-8", errors="replace") as f:
            raw = f.read()
        role, coll = classify(path)
        units.append(
            Unit(
                path=path,
                rel=os.path.relpath(path, root),
                logpath=tuple(
                    os.path.relpath(path, root)[:-2].split(os.sep)
                ),
                role=role,
                collection=coll,
                decls=scan_file(path, raw),
                lines=raw.count("\n") + 1,
            )
        )
    return units


def require_graph(units):
    """path -> set of paths it requires, resolved by longest path suffix.

    A logical path (``New.proof.go_etcd_io.raft.v3_proof.election.defs``)
    and a file path (``new/proof/go_etcd_io/raft/v3_proof/election/defs.v``)
    agree on their tail and disagree on their head, since the logical root is
    declared in _RocqProject rather than in the source.  Matching on the
    longest common tail needs neither.
    """
    by_tail = collections.defaultdict(list)
    for u in units:
        for k in range(1, len(u.logpath) + 1):
            by_tail[u.logpath[-k:]].append(u)
    edges = collections.defaultdict(set)
    for u in units:
        with open(u.path, encoding="utf-8", errors="replace") as f:
            text = strip_comments(f.read())
        for req in requires(text):
            parts = tuple(req.split("."))
            for k in range(len(parts), 0, -1):
                hits = by_tail.get(parts[-k:])
                if hits and len(hits) == 1:
                    if hits[0].path != u.path:
                        edges[u.path].add(hits[0].path)
                    break
    return edges


# --------------------------------------------------------------------------
# What each declaration is


def is_definition(decl):
    """Whether the declaration defines something rather than claiming it."""
    if decl.kind in TYPE_KINDS or decl.kind in ("Definition", "Fixpoint",
                                                "CoFixpoint"):
        return True
    # `Instance foo : C := bar.` and `Example ok : t = u := eq_refl.` define
    # by giving the term; `Instance foo : C. Proof. … Qed.` proves.  Having
    # no proof at all and a `:=` is the tell, and both halves are needed: a
    # statement can hold a `let … :=` and still be proved by a script.
    return (decl.kind in PROVABLE_KINDS and decl.ended is None
            and ":=" in decl.statement)


ALIAS_RE = re.compile(r"^\s*:\s*([A-Za-z_][\w'\u2019.]*)\s*\.\s*$")


def follow_alias(decl, index):
    """The declaration whose text says what `decl` states.

    A collection states its triple once, as ``Definition wp_X_body := …``,
    and the Axiom or Lemma that assumes or proves it is written
    ``wp_X : wp_X_body.``.  To say what such an assumption is *about* you
    have to look through that one indirection.
    """
    seen = set()
    cur = decl
    while True:
        m = ALIAS_RE.match(cur.statement)
        if not m:
            return cur
        tgt = resolve(m.group(1), index, cur.path)
        if tgt is None or (tgt.path, tgt.line) in seen:
            return cur
        seen.add((tgt.path, tgt.line))
        cur = tgt


def assumption_shape(decl):
    """"triple", "property" or "declaration" -- what kind of thing is assumed."""
    if decl.is_triple:
        return "triple"
    if DECLARATION_TAIL_RE.search(decl.statement.strip()):
        return "declaration"
    return "property"


def status_of(decl):
    """What became of one declaration.

    One of "assumed", "admitted", "aborted", "unclosed", "proved",
    "defined" or "obligation".  "unclosed" means no terminator was found,
    which in practice means this tool failed to parse rather than that Rocq
    accepted a proof with no end.
    """
    if decl.kind in ASSUMPTION_KINDS:
        return "obligation" if decl.in_module_type else "assumed"
    if is_definition(decl):
        return "defined"
    if decl.kind in PROVABLE_KINDS:
        if decl.ended == "Admitted":
            return "admitted"
        if decl.ended in ("Qed", "Defined"):
            return "proved"
        return "aborted" if decl.ended == "Abort" else "unclosed"
    return "defined"


def trusted_marker(raw_lines, decl, marker):
    """Whether this assumption is marked as one the development means to keep.

    The marker is looked for on the declaration's own line and on the line
    the proof ends on -- which is where ``Admitted. (* Trusted *)`` puts it,
    and the only two places that cannot be confused with a marker belonging
    to the neighbouring declaration.
    """
    for line in (decl.line, decl.ended_line):
        if line and 0 < line <= len(raw_lines):
            if re.search(marker, raw_lines[line - 1]):
                return True
    return False


# --------------------------------------------------------------------------
# The name index and the reference graph


def build_index(units):
    """Two maps from a written name to the declarations that could define it.

    `by_qual` is keyed by the name as Rocq would write it from the top level
    (``nstate.t``, ``msg.from``), `by_bare` by the last component alone.  A
    record field and an inductive constructor are indexed onto their type:
    reading ``nstate.role`` means reading the record it belongs to.
    """
    by_qual = collections.defaultdict(list)
    by_bare = collections.defaultdict(list)
    for u in units:
        for d in u.decls:
            names = [qualified(d)]
            for sub in rocqscan.sub_names(d.kind, d.statement):
                names.append(".".join(d.modpath + (sub,)))
            for n in names:
                by_qual[n].append(d)
                by_bare[n.split(".")[-1]].append(d)
    return by_qual, by_bare


def resolve(ident, index, home):
    """The declaration `ident` names, or None.

    Tries the qualified spelling first, then the bare last component, which
    is how a name inside its own module is written.  An ambiguous name
    resolves only if exactly one of the candidates is in the file doing the
    referring; otherwise the tool would rather say it does not know, and
    the name is counted as unresolved.
    """
    by_qual, by_bare = index
    for key, table in ((ident, by_qual), (ident.split(".")[-1], by_bare)):
        hits = table.get(key)
        if not hits:
            continue
        if len(hits) == 1:
            return hits[0]
        # Prefer a candidate in the referring file: a bare name usually means
        # the local one.
        local = [d for d in hits if d.path == home]
        if len(local) == 1:
            return local[0]
        return None
    return None


def closure(seeds, index, decl_key):
    """Definitions reachable from the seeds' text, and unresolved references.

    A seed is a statement that has to be read.  Reading it means reading the
    definitions it mentions; reading *those* means reading their bodies,
    because a definition's body is part of what it means.  A lemma or an
    axiom it mentions is not followed: its statement is trusted on its own
    terms and is counted in its own bucket.
    """
    seen, out, unresolved = set(), [], collections.Counter()
    work = list(seeds)
    seeded = {decl_key(d) for d in seeds}
    while work:
        d = work.pop()
        for ident in d.refs:
            tgt = resolve(ident, index, d.path)
            if tgt is None:
                unresolved[ident] += 1
                continue
            key = decl_key(tgt)
            if key in seen or key in seeded:
                continue
            seen.add(key)
            if is_definition(tgt):
                out.append(tgt)
                work.append(tgt)
    return out, unresolved


# --------------------------------------------------------------------------
# The exported surface


def mentions(units, index):
    """(path, line) of a declaration -> the declarations that name it.

    Both the statements and the proof scripts are read, because using a
    lemma in a proof is the ordinary way to use one, and a helper lemma that
    only ever appears in another proof must not be mistaken for a result the
    development exports.  A declaration naming itself does not count.
    """
    out = collections.defaultdict(set)
    for u in units:
        for d in u.decls:
            for ident in set(d.refs) | set(d.proof_refs):
                tgt = resolve(ident, index, d.path)
                if tgt is None or (tgt.path, tgt.line) == (d.path, d.line):
                    continue
                out[(tgt.path, tgt.line)].add((d.path, d.line))
    return out


def exported_surface(units, edges, index, mentioned):
    """The declarations a client of this development has to read.

    Two rules, one for each way a development exposes something:

      * a **collection** that no *other collection* requires or names
        specifies a Go function nothing else in the development calls -- a
        root of the call graph.  Its ``_body`` holds the statement.  An
        aggregator that re-exports every ``link_*`` so that CI builds them
        is deliberately not counted as a caller: re-exporting is not
        calling, and if it were, every collection would look internal.
      * a **declaration** in a file nothing else requires, which nothing
        else names.  That is a theorem stated for its own sake: the payoff,
        or something nobody uses.

    Both are "nothing depends on it", which is what externally facing means
    from inside a development.  Go's export rule is reported alongside, not
    used to decide: an exported method whose spec something else in the
    development calls is an internal callee here, however public it is in Go.
    """
    by_path = {u.path: u for u in units}
    used_by = collections.defaultdict(set)
    for src, dsts in edges.items():
        for dst in dsts:
            used_by[dst].add(src)

    # A collection is internal if another collection requires one of its
    # files, or names one of its declarations.
    internal_colls = set()
    for u in units:
        if not u.collection or u.collection in internal_colls:
            continue
        callers = set()
        for src in used_by.get(u.path, ()):
            other = by_path.get(src)
            if other is not None and other.collection:
                callers.add(other.collection)
        for d in u.decls:
            for path, _line in mentioned.get((d.path, d.line), ()):
                other = by_path.get(path)
                if other is not None and other.collection:
                    callers.add(other.collection)
        if callers - {u.collection}:
            internal_colls.add(u.collection)

    surface = []
    for u in units:
        if u.collection:
            if u.collection in internal_colls or u.role != "spec":
                continue
            for d in u.decls:
                if d.name.endswith(BODY_SUFFIX) or d.is_triple:
                    surface.append((d, u))
                    break
            continue
        if used_by.get(u.path):
            continue  # something requires this file, so it is not an entry
        for d in u.decls:
            if is_definition(d) or d.in_module_type:
                continue
            if mentioned.get((d.path, d.line)):
                continue
            surface.append((d, u))
    return surface, internal_colls


# --------------------------------------------------------------------------
# The report


def build_report(units, edges, scope_dir, root, marker):
    index = build_index(units)
    mentioned = mentions(units, index)
    surface, internal_colls = exported_surface(units, edges, index, mentioned)

    raw_lines = {}
    for u in units:
        with open(u.path, encoding="utf-8", errors="replace") as f:
            raw_lines[u.path] = f.read().split("\n")

    assumed, results, files = [], [], []
    for u in units:
        counts = collections.Counter()
        carried = []
        for d in u.decls:
            st = status_of(d)
            counts[st] += 1
            if st in ("assumed", "admitted"):
                says = follow_alias(d, index)
                rec = {
                    "file": u.rel,
                    "line": d.line,
                    "name": qualified(d),
                    "kind": d.kind,
                    "how": "Axiom" if st == "assumed" else "Admitted",
                    "shape": assumption_shape(says),
                    "go_fns": says.go_fns,
                    "lines": d.lines,
                    "trusted": trusted_marker(raw_lines[u.path], d, marker),
                }
                assumed.append((d, u, rec))
                carried.append(rec)
        files.append((u, counts, carried))

    for d, u in surface:
        says = follow_alias(d, index)
        results.append(
            {
                "file": u.rel,
                "line": d.line,
                "name": qualified(d),
                "kind": d.kind,
                "status": status_of(d),
                "lines": d.lines,
                "go_fns": says.go_fns,
                "exported_in_go": [f for f in says.go_fns if is_exported(f)],
            }
        )

    # The definitions the trusted statements rest on.  Seeds are the exported
    # statements and the statements of everything assumed: to know what an
    # axiom assumes you have to read the definitions it is written in.
    seeds = [d for d, _u in surface] + [d for d, _u, _r in assumed]
    defs, unresolved = closure(seeds, index, lambda d: (d.path, d.line))

    scope_abs = os.path.abspath(scope_dir)

    def in_scope(rel):
        path = os.path.abspath(os.path.join(root, rel))
        # Compare path components, not characters: `election` is not a
        # prefix of `election_protocol.v` in any sense that matters.
        return path == scope_abs or path.startswith(scope_abs + os.sep)

    scoped_units = [f for f in files if in_scope(f[0].rel)]
    scoped_assumed = [r for _d, _u, r in assumed if in_scope(r["file"])]
    scoped_results = [r for r in results if in_scope(r["file"])]
    scoped_defs = [
        d for d in defs if in_scope(os.path.relpath(d.path, root))
    ]

    total_lines = sum(u.lines for u, _c, _k in scoped_units)
    obligations = sum(c["obligation"] for _u, c, _k in scoped_units)
    proved = sum(c["proved"] for _u, c, _k in scoped_units)

    # The three buckets have to be disjoint or the total is a lie.  An
    # exported result that is itself an axiom -- which happens, and is worth
    # seeing -- is counted once, as assumed, and still listed as a result.
    assumed_keys = {(r["file"], r["line"]) for r in scoped_assumed}
    counted_results = [r for r in scoped_results
                       if (r["file"], r["line"]) not in assumed_keys]
    tcb_lines = (
        sum(r["lines"] for r in scoped_assumed)
        + sum(r["lines"] for r in counted_results)
        + sum(d.lines for d in scoped_defs)
    )
    return {
        "scope": os.path.relpath(scope_dir, root),
        "files": len(scoped_units),
        "lines": total_lines,
        "assumed": scoped_assumed,
        "results": scoped_results,
        "definitions": [
            {
                "file": os.path.relpath(d.path, root),
                "line": d.line,
                "name": qualified(d),
                "kind": d.kind,
                "lines": d.lines,
            }
            for d in sorted(scoped_defs, key=lambda d: (d.path, d.line))
        ],
        "results_assumed": len(scoped_results) - len(counted_results),
        "tcb_decls": (len(scoped_assumed) + len(counted_results)
                      + len(scoped_defs)),
        "obligations": obligations,
        "proved": proved,
        "internal_collections": len(internal_colls),
        "tcb_lines": tcb_lines,
        "unresolved": unresolved.most_common(),
        "file_status": [
            {
                "file": u.rel,
                "status": file_status(c),
                "lines": u.lines,
                "counts": dict(c),
                "carries": k,
            }
            for u, c, k in scoped_units
        ],
    }


def file_status(counts):
    """One word for a file, worst first: what a reader most needs to know.

    ``aborted`` and ``unclosed`` are not assumptions -- an ``Abort`` leaves
    nothing behind, and an unclosed one is most likely this tool failing to
    find the terminator -- but both mean a proof that is not there, which is
    what someone looking for the incomplete parts wants to see.
    """
    if counts["admitted"]:
        return "admitted"
    if counts["assumed"]:
        return "assumed"
    if counts["aborted"]:
        return "aborted"
    if counts["unclosed"]:
        return "unclosed"
    if counts["proved"]:
        return "proved"
    if counts["obligation"]:
        return "stated"
    if counts["defined"]:
        return "defs"
    return "plumbing"


# --------------------------------------------------------------------------
# Printing

STATUS_ORDER = ["admitted", "assumed", "aborted", "unclosed", "proved",
                "stated", "defs", "plumbing"]
INCOMPLETE = ("admitted", "assumed", "aborted", "unclosed")

# Room for the longest path in this repository's proof tree plus a little;
# the names that follow are truncated to whatever is left of 100 columns.
PATH_W = 56
WIDTH = 100


def pct(a, b):
    return "{:.1f}%".format(100.0 * a / b) if b else "-"


def num(n):
    return "{:,}".format(n)


def shorten(text, width):
    return text if len(text) <= width else text[: width - 1] + "…"


def shorten_path(path, width):
    """Trim a path from the left: the file name is what identifies it."""
    return path if len(path) <= width else "…" + path[-(width - 1):]


def row(label, count, lines, note, out, indent=2):
    print("{}{:<29}{:>5}  {:>11}   {}".format(
        " " * indent, label, count,
        "{} lines".format(num(lines)) if lines is not None else "",
        note).rstrip(), file=out)


def print_summary(rep, out):
    shapes = collections.Counter(r["shape"] for r in rep["assumed"])
    how = collections.Counter(r["how"] for r in rep["assumed"])
    trusted = sum(1 for r in rep["assumed"] if r["trusted"])
    n_def = len(rep["definitions"])
    def_lines = sum(d["lines"] for d in rep["definitions"])
    assumed_at = {(r["file"], r["line"]) for r in rep["assumed"]}
    res_lines = sum(r["lines"] for r in rep["results"]
                    if (r["file"], r["line"]) not in assumed_at)
    ass_lines = sum(r["lines"] for r in rep["assumed"])

    print("TCB of {}   {} files, {} lines".format(
        rep["scope"], rep["files"], num(rep["lines"])), file=out)
    print(file=out)
    row("assumed", len(rep["assumed"]), ass_lines,
        ", ".join("{} {}".format(n, k) for k, n in sorted(how.items()))
        or "nothing", out)
    for shape, label in (
        ("triple", "Hoare triples about Go code"),
        ("property", "properties of the model"),
        ("declaration", "opaque declarations"),
    ):
        if shapes[shape]:
            print("    {:<29}{:>3}".format(label, shapes[shape]), file=out)
    if trusted:
        print("    {:<29}{:>3}   deliberate, marked in a comment".format(
            "of those, trusted", trusted), file=out)
    row("results", len(rep["results"]) - rep["results_assumed"], res_lines,
        "statements nothing else depends on", out)
    if rep["results_assumed"]:
        print("    {:<29}{:>3}   counted under assumed, not twice".format(
            "more, but assumed", rep["results_assumed"]), file=out)
    row("definitions", n_def, def_lines, "reached from those statements", out)
    print("  " + "-" * 62, file=out)
    row("TCB", rep["tcb_decls"], rep["tcb_lines"],
        "{} of the development".format(pct(rep["tcb_lines"], rep["lines"])),
        out)
    print(file=out)
    print("  not trusted  {:>4}  obligations, each discharged by a functor"
          .format(rep["obligations"]), file=out)
    print("               {:>4}  specs of functions something else calls"
          .format(rep["internal_collections"]), file=out)
    print("               {:>4}  lemmas with a Qed".format(rep["proved"]),
          file=out)
    print(file=out)

    by_status = collections.Counter(f["status"] for f in rep["file_status"])
    print("Files  " + " · ".join(
        "{} {}".format(by_status[s], s) for s in STATUS_ORDER if by_status[s]),
        file=out)
    incomplete = [f for f in rep["file_status"]
                  if f["status"] in INCOMPLETE]
    if incomplete:
        print(file=out)
        print("Incomplete ({} files), under {}:".format(
            len(incomplete), rep["scope"]), file=out)
        for f in sorted(incomplete, key=lambda f: (f["status"], f["file"])):
            c = f["counts"]
            tally = " ".join(
                "{} {}".format(c[k], lbl) for k, lbl in
                (("admitted", "adm"), ("assumed", "ax"),
                 ("aborted", "abort"), ("unclosed", "open")) if c.get(k))
            rel = os.path.relpath(f["file"], rep["scope"])
            names = ", ".join(sorted({c2["name"].split(".")[-1]
                                      for c2 in f["carries"]}))
            print("  {:<{w}} {:<10} {}".format(
                shorten_path(rel, PATH_W), tally,
                shorten(names, WIDTH - PATH_W - 14), w=PATH_W), file=out)


def print_files(rep, out):
    print("{:<{w}} {:<9} {:>6} {:>4} {:>4} {:>6}".format(
        "file", "status", "lines", "ax", "adm", "proved", w=PATH_W), file=out)
    for f in rep["file_status"]:
        c = f["counts"]
        print("{:<{w}} {:<9} {:>6} {:>4} {:>4} {:>6}".format(
            shorten_path(os.path.relpath(f["file"], rep["scope"]), PATH_W),
            f["status"], f["lines"],
            c.get("assumed", 0), c.get("admitted", 0), c.get("proved", 0),
            w=PATH_W), file=out)


def print_assumed(rep, out):
    if not rep["assumed"]:
        print("nothing assumed", file=out)
        return
    print("{:<{w}} {:<9} {:<12} {}".format(
        "where", "how", "shape", "what", w=PATH_W), file=out)
    for r in sorted(rep["assumed"], key=lambda r: (r["file"], r["line"])):
        what = r["name"]
        if r["go_fns"]:
            what += "  [{}]".format(", ".join(r["go_fns"]))
        if r["trusted"]:
            what += "  (trusted)"
        where = "{}:{}".format(os.path.relpath(r["file"], rep["scope"]),
                               r["line"])
        print("{:<{w}} {:<9} {:<12} {}".format(
            shorten_path(where, PATH_W), r["how"], r["shape"], what, w=PATH_W),
            file=out)


def print_surface(rep, out):
    print("Externally-facing results ({}):".format(len(rep["results"])),
          file=out)
    for r in sorted(rep["results"], key=lambda r: (r["file"], r["line"])):
        note = r["status"]
        if r["exported_in_go"]:
            note += ", exported in Go"
        elif r["go_fns"]:
            note += ", unexported in Go"
        where = "{}:{}".format(os.path.relpath(r["file"], rep["scope"]),
                               r["line"])
        print("  {:<{w}} {:<34} {:>3} lines  [{}]".format(
            shorten_path(where, PATH_W), shorten(r["name"], 34), r["lines"], note,
            w=PATH_W), file=out)
    print(file=out)
    print("Definitions they rest on ({}, {} lines):".format(
        len(rep["definitions"]),
        num(sum(d["lines"] for d in rep["definitions"]))), file=out)
    by_file = collections.defaultdict(list)
    for d in rep["definitions"]:
        by_file[d["file"]].append(d)
    for path in sorted(by_file):
        ds = by_file[path]
        print("  {:<{w}} {:>3} defs, {:>4} lines".format(
            shorten_path(os.path.relpath(path, rep["scope"]), PATH_W), len(ds),
            sum(d["lines"] for d in ds), w=PATH_W), file=out)
        print("      " + shorten(", ".join(d["name"] for d in ds), WIDTH - 6),
              file=out)
    unres = rep["unresolved"]
    print(file=out)
    print("{} distinct names in those statements resolve to nothing in this "
          "tree:".format(len(unres)), file=out)
    print("  binders, and Perennial/stdpp/Rocq constants, which are trusted "
          "too and not counted here.", file=out)
    if unres:
        print("  most frequent: " + shorten(", ".join(
            "{} ({}x)".format(name, n) for name, n in unres[:10]), WIDTH - 17),
            file=out)


# --------------------------------------------------------------------------


def resolve_scope(scope, proof_root):
    """The directory to report on: all of the proof root, a path, or a name."""
    if not scope:
        return proof_root
    for cand in (scope, os.path.join(proof_root, scope)):
        if os.path.isdir(cand):
            return os.path.abspath(cand)
    matches = sorted(
        dp
        for dp, _dirs, _f in os.walk(proof_root)
        if os.path.basename(dp) == scope
    )
    if len(matches) == 1:
        return matches[0]
    if not matches:
        sys.exit("no directory named {!r} under {} (and no such path)".format(
            scope, proof_root))
    sys.exit("{!r} is ambiguous under {}:\n  {}".format(
        scope, proof_root, "\n  ".join(matches)))


# --------------------------------------------------------------------------
# Self-test: a miniature development with one of everything, so that the
# buckets are pinned down by an example rather than by prose.

SELFTEST_FILES = {
    "model.v": '''\
Module st.
Record t := mk { term : nat ; leader : bool }.
End st.

Definition legal (s s' : st.t) : Prop := st.term s <= st.term s'.

Axiom own_state : st.t -> iProp.
Axiom own_state_agree : forall s s', own_state s -* own_state s' -* legal s s'.
''',
    "spec_f.v": '''\
Require Export model.
Definition wp_f_body := {{{ own_state s }}} @! pkg.f #x {{{ RET #(); True }}}.
Module Type F.
  Parameter wp_f : wp_f_body.
End F.
''',
    "proof_f.v": '''\
Require Export spec_f.
Module FProof : F.
  Lemma wp_f : wp_f_body.
  Proof. reflexivity. Qed.
End FProof.
''',
    "spec_G.v": '''\
Require Export model.
Definition wp_G_body := {{{ own_state s }}} r @! (go.PointerType pkg.T) @! "G" #x {{{ RET #(); legal s s }}}.
Module Type G.
  Parameter wp_G : wp_G_body.
End G.
''',
    "proof_G.v": '''\
Require Export spec_G.
Require Export spec_f.
Module GProof (P : F) : G.
  Lemma wp_G : wp_G_body.
  Proof. apply wp_f. Admitted.
  Example refl_ok : legal s s := eq_refl.
End GProof.
''',
}


def selftest():
    import tempfile

    bad = []
    rc = rocqscan.selftest()
    with tempfile.TemporaryDirectory() as d:
        root = os.path.join(d, "dev")
        os.makedirs(root)
        for name, body in SELFTEST_FILES.items():
            with open(os.path.join(root, name), "w") as f:
                f.write(body)
        units = load(root, d)
        edges = require_graph(units)
        rep = build_report(units, edges, root, d, TRUSTED_MARKER)

        def want(cond, what):
            if not cond:
                bad.append("tcb: " + what)

        names = {r["name"] for r in rep["assumed"]}
        # Both axioms are assumed; the Parameters in the two Module Types are
        # not, and neither is the Qed'd lemma.
        want(names == {"own_state", "own_state_agree", "GProof.wp_G"},
             "assumed = {}".format(sorted(names)))
        shapes = {r["name"]: r["shape"] for r in rep["assumed"]}
        want(shapes.get("own_state") == "declaration", "opaque declaration")
        want(shapes.get("own_state_agree") == "property", "property")
        want(shapes.get("GProof.wp_G") == "triple", "admitted triple")
        want(rep["obligations"] == 2, "obligations = {}".format(rep["obligations"]))
        # G calls f, so f's collection is internal and only G is exported.
        results = {r["name"] for r in rep["results"]}
        want(results == {"wp_G_body"}, "results = {}".format(sorted(results)))
        want([r["exported_in_go"] for r in rep["results"]] == [["pkg.T.G"]],
             "Go export rule reported")
        # The statements rest on `legal`, `st.t` (through `st.term`) and the
        # `_body` of the admitted triple -- but not on `wp_f_body`, which
        # nothing trusted mentions.
        defs = {d["name"] for d in rep["definitions"]}
        want("legal" in defs and "st.t" in defs,
             "definition closure = {}".format(sorted(defs)))
        want("wp_f_body" not in defs, "internal spec not in the closure")
        # a definition by term is not an unfinished proof
        want(not any(f["counts"].get("unclosed")
                     for f in rep["file_status"]),
             "Example ... := term read as unclosed")
        statuses = {f["file"]: f["status"] for f in rep["file_status"]}
        want(statuses == {
            "dev/model.v": "assumed",
            "dev/spec_f.v": "stated",
            "dev/proof_f.v": "proved",
            "dev/spec_G.v": "stated",
            "dev/proof_G.v": "admitted",
        }, "file status = {}".format(statuses))

    for b in bad:
        print("FAIL " + b)
    print("tcb-report selftest: {}".format(
        "{} failures".format(len(bad)) if bad else "ok"))
    return 1 if (bad or rc) else 0


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--root", default=".",
                    help="repository root (default: the current directory)")
    ap.add_argument("--proof-root", default=DEFAULT_PROOF_ROOT,
                    help="the development to look at, relative to --root "
                         "(default: {})".format(DEFAULT_PROOF_ROOT))
    ap.add_argument("--scope", default=None,
                    help="restrict the report to a path, or to the bare name "
                         "of a directory anywhere under the proof root.  The "
                         "graph is still built from the whole proof root, so "
                         "scoping cannot invent exported results")
    ap.add_argument("--view", choices=["summary", "files", "assumed",
                                       "surface", "all"], default="summary")
    ap.add_argument("--format", choices=["text", "json"], default="text")
    ap.add_argument("--trusted-marker", default=TRUSTED_MARKER,
                    help="regex marking a deliberate assumption in a comment "
                         "(default: {})".format(TRUSTED_MARKER))
    ap.add_argument("--selftest", action="store_true",
                    help="check the classification on a miniature development")
    args = ap.parse_args()

    if args.selftest:
        return selftest()

    root = os.path.abspath(args.root)
    proof_root = os.path.join(root, args.proof_root)
    if not os.path.isdir(proof_root):
        sys.exit("no such proof root: {}".format(proof_root))
    scope_dir = resolve_scope(args.scope, proof_root)

    units = load(proof_root, root)
    edges = require_graph(units)
    rep = build_report(units, edges, scope_dir, root, args.trusted_marker)

    if args.format == "json":
        print(json.dumps(rep, indent=2))
        return 0

    out = sys.stdout
    if args.view in ("summary", "all"):
        print_summary(rep, out)
    if args.view in ("files", "all"):
        print(file=out) if args.view == "all" else None
        print_files(rep, out)
    if args.view in ("assumed", "all"):
        print(file=out) if args.view == "all" else None
        print_assumed(rep, out)
    if args.view in ("surface", "all"):
        print(file=out) if args.view == "all" else None
        print_surface(rep, out)
    return 0


if __name__ == "__main__":
    sys.exit(main())
