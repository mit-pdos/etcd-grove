#!/usr/bin/env python3
"""Render Rocq files down to their trust base.

Reviewing what the raft proof *assumes* means reading every ``Axiom``, every
``Admitted.``, and every definition that appears in a top-level theorem's
statement --- and ignoring everything else.  This tool does that filtering
mechanically: it prints the top-level theorems, the transitive closure of the
definitions their statements mention, and every assumption, while hiding proof
bodies and proved helper lemmas entirely.

It is purely textual.  It never runs Rocq and needs no build, so it works on any
checkout, but it therefore reports the trust boundary *as written in the files
you point it at* --- it cannot see assumptions inherited from Perennial, Iris or
the Goose semantics.  ``Print Assumptions`` remains the only ground truth.

Usage:

    ./etc/tcb-view.py new/proof/go_etcd_io/raft
    ./etc/tcb-view.py --summary new/proof/go_etcd_io/raft
    ./etc/tcb-view.py new/proof/go_etcd_io/raft/v3_proof/election.v
    ./etc/tcb-view.py --self-check
"""

import os
import re
import sys
from dataclasses import dataclass, field

# --------------------------------------------------------------------------
# Lexing
#
# Rocq sentences end at a "." that is followed by whitespace or EOF and is not
# inside a comment or a string.  That single rule handles the qualified names
# and record projections that are everywhere in this corpus --- s.(nstate.term),
# m.(raftpb.Message.Type'), raft.raft.t, N.@"commit" --- without special cases.
# Comments nest, and (as in Rocq itself) a '"' inside a comment opens a string.
# --------------------------------------------------------------------------


def _skip_string(src, i):
    """Index just past the string literal starting at src[i] == '"'."""
    n = len(src)
    i += 1
    while i < n:
        if src[i] == '"':
            if i + 1 < n and src[i + 1] == '"':
                i += 2  # "" is an escaped quote
                continue
            return i + 1
        i += 1
    return n


def _skip_comment(src, i):
    """Index just past the comment starting at src[i:i+2] == '(*'."""
    n = len(src)
    depth = 0
    while i < n:
        if src.startswith("(*", i):
            depth += 1
            i += 2
        elif src.startswith("*)", i):
            depth -= 1
            i += 2
            if depth == 0:
                return i
        elif src[i] == '"':
            i = _skip_string(src, i)
        else:
            i += 1
    return n


def _skip_sentence(src, i):
    """Index just past the sentence starting at src[i]."""
    n = len(src)
    while i < n:
        if src.startswith("(*", i):
            i = _skip_comment(src, i)
        elif src[i] == '"':
            i = _skip_string(src, i)
        elif src[i] == ".":
            j = i + 1
            if j >= n or src[j].isspace():
                return j
            i = j
        else:
            i += 1
    return n


def scan_segments(src):
    """Split src into ("ws"|"comment"|"sentence", start, end) tiling all of it."""
    segs = []
    i = 0
    n = len(src)
    while i < n:
        if src[i].isspace():
            j = i
            while j < n and src[j].isspace():
                j += 1
            segs.append(("ws", i, j))
        elif src.startswith("(*", i):
            j = _skip_comment(src, i)
            segs.append(("comment", i, j))
        else:
            j = _skip_sentence(src, i)
            segs.append(("sentence", i, j))
        if j <= i:  # defensive: never loop forever on a malformed file
            j = i + 1
            segs.append(("ws", i, j))
        i = j
    return segs


# --------------------------------------------------------------------------
# Sentence classification
# --------------------------------------------------------------------------

# Leading proof-structure punctuation: bullets, braces, "2:{", "[", "|".
_FOCUS_RE = re.compile(r"^(?:\s|[-+*{}\[\]|]|\d+\s*:)+")
# Attributes and modifiers that precede the real keyword.
_ATTR_RE = re.compile(
    r"^(?:#\[[^\]]*\]\s*|(?:Local|Global|Program|Time|Polymorphic|Monomorphic)\s+)*"
)
_IDENT_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")
_QUALID_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*")

STRUCTURAL_KW = {
    "From", "Require", "Import", "Export", "Section", "End", "Module",
    "Context", "Implicit", "Collection", "Set", "Unset", "Arguments", "Hint",
    "Open", "Close", "Existing", "Declare", "Notation", "Reserved", "Include",
    "Bind", "Coercion", "Canonical", "Opaque", "Transparent", "Typeclasses",
    "Add", "Create", "Generalizable", "Scheme",
}  # fmt: skip
ASSUMED_KW = {
    "Axiom", "Axioms", "Parameter", "Parameters", "Hypothesis", "Hypotheses",
    "Variable", "Variables", "Conjecture",
}  # fmt: skip
PROVABLE_KW = {
    "Lemma", "Theorem", "Corollary", "Remark", "Fact", "Proposition",
    "Property", "Goal", "Example",
}  # fmt: skip
DEFINITIONAL_KW = {
    "Definition", "Fixpoint", "CoFixpoint", "Inductive", "CoInductive",
    "Variant", "Record", "Structure", "Class", "Instance", "Let", "Function",
    "Equations",
}  # fmt: skip
TACTIC_KW = {"Ltac", "Ltac2"}
TERMINATOR_KW = {"Qed", "Admitted", "Defined", "Abort", "Save"}
ROOT_KW = {"Theorem", "Corollary"}

# Not expected in this corpus; warn rather than mis-parse silently.
UNEXPECTED_KW = {"Program", "Obligation", "Obligations"}

DISABLE_QED_MARK = "Unshelve. Fail idtac. Admitted."


def head_tokens(text, count=4):
    """Leading identifier tokens of a sentence, past punctuation and attributes."""
    t = _FOCUS_RE.sub("", text)
    while t.startswith("(*"):
        t = t[_skip_comment(t, 0) :].lstrip()
    t = _ATTR_RE.sub("", t)
    return _IDENT_RE.findall(t)[:count]


def strip_comments(text):
    """text with all comments replaced by a space (for identifier extraction)."""
    out = []
    i = 0
    n = len(text)
    while i < n:
        if text.startswith("(*", i):
            i = _skip_comment(text, i)
            out.append(" ")
        elif text[i] == '"':
            j = _skip_string(text, i)
            out.append(" ")
            i = j
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def classify_keyword(tokens):
    """(kind, keyword) for a sentence's head tokens, or (None, None)."""
    if not tokens:
        return None, None
    kw = tokens[0]
    if kw in ASSUMED_KW:
        return "assumed", kw
    if kw in PROVABLE_KW:
        return "provable", kw
    if kw in DEFINITIONAL_KW:
        return "definitional", kw
    if kw in TACTIC_KW:
        return "tactic", kw
    if kw == "Tactic" and len(tokens) > 1 and tokens[1] == "Notation":
        return "tactic", "Tactic Notation"
    if kw in STRUCTURAL_KW:
        return "structural", kw
    return None, None


# --------------------------------------------------------------------------
# Units
# --------------------------------------------------------------------------


@dataclass
class Unit:
    path: str
    kind: str  # structural | assumed | provable | definitional | tactic | comment
    keyword: str
    names: list = field(default_factory=list)
    lead: str = ""  # attached comment block, verbatim
    stmt: str = ""  # declaration sentence, verbatim
    body: str = ""  # proof body between Proof. and the terminator
    terminator: str = ""  # Qed | Admitted | Defined | ""
    term_comment: str = ""  # same-line comment after the terminator
    line: int = 0
    scope: str = ""  # enclosing Section/Module, for the report
    admits: int = 0  # interior `admit.` tactics
    cls: str = "internal"  # internal | root | spec | assumed | always
    is_root: bool = False  # a closure root; orthogonal to cls, since a
    # Theorem can be both a root and an admitted hole

    @property
    def name(self):
        if not self.names:
            return "<anonymous>"
        if self.scope.startswith("Module ") and len(self.names) > 1:
            return self.names[-1]  # module-qualified, e.g. node.t
        return self.names[0]

    @property
    def is_obligation(self):
        """A Parameter inside a `Module Type` is not an assumption.

        It is a proof obligation on whatever implements the signature: a
        functor that discharges it contributes nothing to `Print
        Assumptions`.  Counting these as axioms would report a spec file as
        trusted, which is backwards -- the Module Type is the thing being
        audited, not something being taken on faith.
        """
        return self.kind == "assumed" and self.scope.startswith("Module Type ")

    @property
    def is_hole(self):
        # Obligations still seed the closure (their statements mention the
        # _body definitions, which the reader does need to see); they are
        # just not counted as trusted.  See render_summary.
        return self.kind == "assumed" or self.terminator == "Admitted"

    @property
    def deliberate(self):
        """An Admitted marked `(* Trusted *)` is an assumption, not a gap."""
        return "trusted" in self.term_comment.lower()


def _line_of(src, pos):
    return src.count("\n", 0, pos) + 1


def _names_of(kind, keyword, stmt, modpath):
    """Declared names, module-qualified, plus constructors and record fields."""
    body = strip_comments(stmt)
    after = _ATTR_RE.sub("", _FOCUS_RE.sub("", body))
    after = after.removeprefix(keyword)
    if after.lstrip().startswith(":"):
        # Anonymous, e.g. base.v's `#[global] Instance : IsPkgInit raftpb := ...`.
        return []
    m = _IDENT_RE.search(after)
    if not m:
        return []
    primary = [m.group(0)]
    if keyword in ("Inductive", "Variant", "CoInductive"):
        # Constructors are referenced by name in statements.
        primary += re.findall(r"\|\s*([A-Za-z_][A-Za-z0-9_']*)", body)
    if keyword in ("Record", "Structure", "Class"):
        primary += re.findall(r"^\s*([A-Za-z_][A-Za-z0-9_']*)\s*:", body, re.MULTILINE)
    out = []
    for nm in primary:
        out.append(nm)
        for i in range(len(modpath)):
            out.append(".".join(modpath[i:] + [nm]))
    return out


def parse_file(path, src):
    """Parse src into units.  Raises ValueError if the round trip is not exact."""
    segs = scan_segments(src)
    if "".join(src[a:b] for _, a, b in segs) != src:
        raise ValueError("lexer lost text")

    units = []
    modpath = []
    scope = []
    i = 0
    pending = []  # (kind, start, end) seen since the last unit
    warnings = []

    def flush_standalone(upto):
        """Comment blocks not attached to a declaration become their own units."""
        for kind, a, b in pending[:upto]:
            if kind == "comment":
                units.append(
                    Unit(
                        path=path,
                        kind="comment",
                        keyword="",
                        lead="",
                        stmt=src[a:b],
                        line=_line_of(src, a),
                        scope=scope[-1] if scope else "",
                        cls="always",
                    )
                )

    while i < len(segs):
        kind, a, b = segs[i]
        if kind in ("ws", "comment"):
            pending.append(segs[i])
            i += 1
            continue

        text = src[a:b]
        tokens = head_tokens(text)
        dkind, keyword = classify_keyword(tokens)
        if dkind is None:
            # A sentence that opens no declaration (stray tactic, bullet).  Keep
            # it verbatim rather than dropping it.
            flush_standalone(len(pending))
            pending = []
            units.append(
                Unit(
                    path=path,
                    kind="structural",
                    keyword="",
                    stmt=text,
                    line=_line_of(src, a),
                    scope=scope[-1] if scope else "",
                    cls="always",
                )
            )
            i += 1
            continue

        if tokens[0] in UNEXPECTED_KW:
            warnings.append(f"{path}:{_line_of(src, a)}: unexpected `{tokens[0]}`")

        # Attach a comment block that sits directly above (at most one newline
        # between it and the declaration).  Anything further up is standalone.
        split = len(pending)
        j = len(pending) - 1
        if j >= 0 and pending[j][0] == "ws" and src.count("\n", *pending[j][1:]) <= 1:
            j -= 1
            while j >= 0 and pending[j][0] == "comment":
                split = j
                j -= 1
                if j >= 0 and pending[j][0] == "ws":
                    if src.count("\n", *pending[j][1:]) > 1:
                        break
                    j -= 1
        flush_standalone(split)
        lead = "".join(src[x:y] for _, x, y in pending[split:]).strip()
        pending = []

        # Track Section/Module nesting.
        if keyword in ("Section", "Module") and len(tokens) > 1:
            # `Module Type FOO` is not `Module FOO`: a Parameter in the former
            # is a proof obligation, in the latter an assumption.
            is_modtype = keyword == "Module" and tokens[1] == "Type"
            nm = (tokens[2:] or [""])[0] if is_modtype else tokens[1]
            scope.append(("Module Type " if is_modtype else f"{keyword} ") + nm)
            if keyword == "Module":
                modpath.append(nm)
        elif keyword == "End":
            if scope:
                popped = scope.pop()
                if popped.startswith("Module ") and modpath:
                    modpath.pop()

        unit = Unit(
            path=path,
            kind=dkind,
            keyword=keyword,
            names=_names_of(dkind, keyword, text, modpath),
            lead=lead,
            stmt=text,
            line=_line_of(src, a),
            scope=scope[-1] if scope else "",
        )
        i += 1

        # Consume an attached proof, if the next real sentence opens one.
        k = i
        while k < len(segs) and segs[k][0] in ("ws", "comment"):
            k += 1
        if k < len(segs):
            ntext = src[segs[k][1] : segs[k][2]]
            if head_tokens(ntext)[:1] == ["Proof"]:
                body_parts = []
                k += 1
                while k < len(segs):
                    skind, sa, sb = segs[k]
                    stext = src[sa:sb]
                    if skind == "sentence":
                        toks = head_tokens(stext)
                        if toks and toks[0] in TERMINATOR_KW:
                            unit.terminator = toks[0]
                            k += 1
                            # A same-line trailing comment belongs to the
                            # terminator: `Admitted. (* Trusted *)`.
                            if (
                                k + 1 < len(segs)
                                and segs[k][0] == "ws"
                                and "\n" not in src[segs[k][1] : segs[k][2]]
                                and segs[k + 1][0] == "comment"
                            ):
                                unit.term_comment = src[segs[k + 1][1] : segs[k + 1][2]]
                                k += 2
                            break
                    body_parts.append(stext)
                    k += 1
                unit.body = "".join(body_parts)
                unit.admits = len(re.findall(r"\badmit\b", strip_comments(unit.body)))
                i = k
        units.append(unit)

    return units, warnings


# --------------------------------------------------------------------------
# Reachability
# --------------------------------------------------------------------------


def build_index(units):
    index = {}
    for u in units:
        for nm in u.names:
            index.setdefault(nm, []).append(u)
    return index


def referenced(stmt, index):
    """Units whose names appear in stmt (comments and strings excluded)."""
    hits = []
    for qualid in _QUALID_RE.findall(strip_comments(stmt)):
        parts = qualid.split(".")
        for lo in range(len(parts)):
            key = ".".join(parts[lo:])
            if key in index:
                hits.extend(index[key])
    return hits


def classify(units, extra_roots):
    """Assign .cls to every unit.  Returns the list of root units."""
    index = build_index(units)
    roots, seeds = [], []

    for u in units:
        if u.kind in ("structural", "comment") or u.keyword in (
            "Instance",
            "Notation",
        ):
            # Ambient, or invisible to a name-based graph: always show.
            u.cls = "always"
            continue
        if u.kind == "provable" and (
            u.keyword in ROOT_KW or any(n in extra_roots for n in u.names)
        ):
            u.is_root = True
            u.cls = "root"
            roots.append(u)
            seeds.append(u)
        if u.is_hole:
            # A root can also be a hole; the hole classification wins for
            # rendering, but it stays in the roots list.
            u.cls = "assumed"
            if not u.is_root:
                seeds.append(u)

    # BFS over statements only --- never over proof bodies.
    frontier = list(seeds)
    seen = {id(u) for u in seeds}
    while frontier:
        u = frontier.pop()
        for dep in referenced(u.stmt, index):
            if id(dep) in seen:
                continue
            seen.add(id(dep))
            if dep.cls == "internal":
                if dep.kind == "definitional":
                    dep.cls = "spec"
                else:
                    continue  # a proved lemma's statement is not trusted
            frontier.append(dep)

    return roots


# --------------------------------------------------------------------------
# Rendering
# --------------------------------------------------------------------------


def fold(u, opts):
    """The rendered text of one shown unit."""
    out = []
    if u.lead and not opts.no_comments:
        out.append(u.lead)
    out.append(u.stmt)
    if u.terminator == "Admitted":
        note = "HOLE"
        if u.deliberate:
            note = "ASSUMED ON PURPOSE"
        if u.admits:
            note += f" | {u.admits} interior admit."
        tail = f"Admitted. (* {note} *)"
        out.append(tail)
    elif u.terminator:
        body = " ".join(u.body.split())
        if len(body) <= 60:
            # A one-liner proof is shorter than a note saying how long it is.
            out.append(f"Proof. {body} {u.terminator}.".replace("  ", " "))
        else:
            n = u.body.count("\n") + 1
            out.append(f"Proof. (* {n} lines *) {u.terminator}.")
    return "\n".join(out)


def render_file(path, units, opts, out):
    shown = [u for u in units if u.cls != "internal"]
    hidden = [u for u in units if u.cls == "internal"]
    axioms = [u for u in units if u.kind == "assumed" and not u.is_obligation]
    obligs = [u for u in units if u.is_obligation]
    admits = [u for u in units if u.terminator == "Admitted"]
    roots = [u for u in units if u.is_root]
    total = sum(u.stmt.count("\n") + u.body.count("\n") + 2 for u in units)

    out.append(f"(* ======== {path} ======== *)")
    rootnames = ", ".join(u.name for u in roots) or "none in this file"
    out.append(f"(* roots: {rootnames} *)")
    ob = f"{len(obligs)} module-type obligations | " if obligs else ""
    out.append(
        f"(* {len(axioms)} axioms | {ob}{len(admits)} admitted | "
        f"{len(hidden)} internal declarations hidden *)"
    )
    out.append("")

    prev = None
    for u in shown:
        text = fold(u, opts)
        if not text.strip():
            continue
        if prev is not None:
            oneline = "\n" not in text and "\n" not in prev
            out.append("" if not oneline else None)
        out.append(text)
        prev = text
    out[:] = [x for x in out if x is not None]

    if hidden and not opts.summary:
        names = sorted({u.name for u in hidden})
        out.append("")
        out.append(f"(* {len(hidden)} internal declarations hidden:")
        line = "   "
        for nm in names:
            if len(line) + len(nm) > 76:
                out.append(line)
                line = "   "
            line += nm + " "
        out.append(line.rstrip())
        out.append("*)")
    out.append("")
    _ = total


def render_summary(allunits, out):
    axioms = [u for u in allunits if u.kind == "assumed" and not u.is_obligation]
    obligs = [u for u in allunits if u.is_obligation]
    admits = [u for u in allunits if u.terminator == "Admitted"]

    out.append("(* ======== TRUST BASE ======== *)")
    out.append("")
    out.append(f"AXIOMS ({len(axioms)})")
    cur = None
    for u in axioms:
        head = f"  {u.path}  [{u.scope or 'top level'}]"
        if head != cur:
            out.append("")
            out.append(head)
            cur = head
        out.append(f"    :{u.line:<5} {u.name}")

    deliberate = [u for u in admits if u.deliberate]
    unfinished = [u for u in admits if not u.deliberate]
    out.append("")
    out.append(f"ADMITTED ({len(admits)})")
    out.append("")
    out.append(f"  assumed on purpose, marked (* Trusted *) ({len(deliberate)})")
    for u in deliberate:
        out.append(f"    {u.path}:{u.line}  {u.name}")
    out.append("")
    out.append(f"  unfinished ({len(unfinished)})")
    for u in unfinished:
        extra = f"  ({u.admits} interior admit.)" if u.admits else ""
        out.append(f"    {u.path}:{u.line}  {u.name}{extra}")

    if obligs:
        by_sig = {}
        for u in obligs:
            by_sig.setdefault(u.scope, []).append(u)
        out.append("")
        out.append(f"MODULE TYPE OBLIGATIONS ({len(obligs)}) -- NOT trusted")
        out.append("")
        out.append("  Each is discharged by the functor ascribed to its signature,")
        out.append("  so none of these reaches `Print Assumptions`.  Listed so that")
        out.append("  the count of specs can be checked against the count of")
        out.append("  functions: one Parameter per function is the invariant.")
        for sig in sorted(by_sig):
            out.append("")
            out.append(f"  {sig}")
            for u in by_sig[sig]:
                out.append(f"    {u.path}:{u.line}  {u.name}")

    out.append("")
    out.append("(* Textual only: this is the trust boundary as written in the files")
    out.append("   given.  It does NOT include assumptions inherited from Perennial,")
    out.append("   Iris, the Goose translator (goose/README.md:8), new/trusted_code/")
    out.append("   or new/golang/defn/.  Only `Print Assumptions` is ground truth. *)")
    out.append("")


# --------------------------------------------------------------------------
# Driver
# --------------------------------------------------------------------------


def collect_paths(targets):
    paths = []
    for t in targets:
        if os.path.isdir(t):
            for root, _, files in os.walk(t):
                paths.extend(
                    os.path.join(root, f) for f in sorted(files) if f.endswith(".v")
                )
        else:
            paths.append(t)
    return paths


def read_source(path):
    if path == "-":
        return sys.stdin.read()
    # surrogateescape keeps the round trip exact even for the handful of
    # generated files that are not valid UTF-8 (e.g. new/code/math/bits.v).
    with open(path, encoding="utf-8", errors="surrogateescape") as f:
        return f.read()


def run(opts):
    paths = collect_paths(opts.targets)
    if not paths:
        sys.stderr.write("tcb-view: no .v files found\n")
        return 1

    per_file, allunits, warnings = [], [], []
    for p in paths:
        src = read_source(p)
        if DISABLE_QED_MARK in src:
            sys.stderr.write(
                f"tcb-view: {p} looks like `make skip-qed` output "
                f"(etc/disable-qed.sh rewrote Qed. to Admitted.).\n"
                f"          Run `make unskip-qed` first; the trust base would "
                f"otherwise be reported as every proof in the file.\n"
            )
            return 2
        units, warn = parse_file(p, src)
        warnings.extend(warn)
        per_file.append((p, units))
        allunits.extend(units)

    classify(allunits, set(opts.root))
    if not any(u.is_root for u in allunits):
        sys.stderr.write(
            "tcb-view: no Theorem/Corollary found in the given files; showing only\n"
            "          assumptions and what they reach.  Name a root explicitly with\n"
            "          --root NAME (v3.v's public surface is `Lemma wp_Node__Propose`).\n"
        )
    for w in warnings:
        sys.stderr.write(f"tcb-view: {w}\n")

    out = []
    if not opts.summary:
        for p, units in per_file:
            render_file(p, units, opts, out)
    render_summary(allunits, out)
    sys.stdout.write("\n".join(out) + "\n")
    return 0


# --------------------------------------------------------------------------
# Self-check
#
# Deliberately built into the tool rather than a separate etc/test_*.py: the
# repo already has etc/test_coqc.py, which nothing runs and which has rotted to
# the point of being unimportable (it does `from coqc import ...`, but the
# module was renamed rocqc.py).  A test nobody runs reads as coverage it does
# not provide.
# --------------------------------------------------------------------------

RAFT_DIR = "new/proof/go_etcd_io/raft"
EXPECTED_AXIOMS = {
    "v3.v": 0,
    "base.v": 0,
    "protocol.v": 6,
    "readonly.v": 7,
    "election_protocol.v": 11,
    # election.v is an aggregator now; the election trust base lives in the
    # inv_*.v files, which is the point -- an Axiom there means "out of
    # scope", an Admitted in a proof_*.v means "in scope but unfinished".
    "election.v": 0,
    "defs.v": 0,
    "inv_raftlog.v": 5,
    "inv_tracker.v": 7,
    "inv_logger.v": 3,
    "inv_misc.v": 10,
    "inv_raft_phys.v": 0,
    "step_lemmas.v": 0,
}
EXPECTED_ADMITS = {
    "v3.v": 0,
    "base.v": 0,
    "protocol.v": 2,
    "readonly.v": 5,
    "election_protocol.v": 0,
    "election.v": 0,
    "proof_raft__reset.v": 1,
    "proof_raft__poll.v": 1,
    "proof_raft__campaign.v": 1,
    "proof_raft__hup.v": 1,
    "proof_stepCandidate_MsgVoteResp.v": 1,
    "proof_raft__Step_MsgVote.v": 1,
    "proof_raft__Step_MsgVoteResp.v": 1,
}
# The whole point of the spec/postulates/proof/link layout: one spec file per
# function, one Parameter in it, and nothing trusted anywhere in it.
EXPECTED_TOTALS = {"axioms": 49, "obligations": 14, "admitted": 14}

FIXTURES = [
    # (source, check name, predicate over units)
    (
        "Lemma a : True.\nProof. solve_decision. Defined.\n",
        "one-liner Defined proof",
        lambda us: us[0].terminator == "Defined" and us[0].names == ["a"],
    ),
    (
        "Lemma a : True.\nProof using.\ndone.\nQed.\n",
        "Proof using",
        lambda us: us[0].terminator == "Qed",
    ),
    (
        'Set Default Proof Using "W".\nLemma a : True.\nProof. done. Qed.\n',
        "Set Default Proof Using is not a proof opener",
        lambda us: len(us) == 2 and us[0].kind == "structural",
    ),
    (
        "Lemma a : True.\nProof.\nAdmitted. (* Trusted *)\n",
        "Admitted. (* Trusted *)",
        lambda us: us[0].deliberate and us[0].is_hole,
    ),
    (
        "Axiom wp_f : {{{ True }}} f {{{ RET #(); True }}}.\n",
        "{{{ }}} inside an Axiom",
        lambda us: us[0].kind == "assumed" and us[0].names == ["wp_f"],
    ),
    (
        "Definition d : nat := (* inline *) 3.\n",
        "comment inside a definition body",
        lambda us: us[0].kind == "definitional" and us[0].names == ["d"],
    ),
    (
        "#[global] Instance : IsPkgInit raftpb := define_is_pkg_init True%I.\n",
        "anonymous Instance",
        lambda us: us[0].keyword == "Instance" and us[0].names == [],
    ),
    (
        'Definition s := "a.b"%go.\nLemma a : True.\nProof. done. Qed.\n',
        "dot inside a string literal",
        lambda us: len(us) == 2,
    ),
    (
        "Module m.\nAxiom t : Type.\nEnd m.\n",
        "module-qualified name",
        lambda us: "m.t" in us[1].names,
    ),
    (
        "Lemma a : True.\nProof.\nadmit.\nadmit.\nAdmitted.\n",
        "interior admit. counting",
        lambda us: us[0].admits == 2,
    ),
    (
        "Module Type FOO.\nParameter wp_f : wp_f_body.\nEnd FOO.\n",
        "Parameter in a Module Type is an obligation, not an axiom",
        lambda us: us[1].is_obligation and us[1].scope == "Module Type FOO",
    ),
    (
        "Module Foo : FOO.\nAxiom wp_f : wp_f_body.\nEnd Foo.\n",
        "Axiom in an ascribed Module is still an axiom",
        lambda us: not us[1].is_obligation and us[1].kind == "assumed",
    ),
]


def self_check(repo_root):
    failures = []

    # 1. Fixtures for each known parser hazard.
    for src, name, pred in FIXTURES:
        try:
            units, _ = parse_file("<fixture>", src)
            decls = [u for u in units if u.kind != "comment"]
            if not pred(decls):
                failures.append(f"fixture failed: {name}")
        except Exception as exc:  # noqa: BLE001 - report, don't abort the sweep
            failures.append(f"fixture raised on {name}: {exc}")

    # 2. Round trip must be byte exact over every .v file in the repo.  This
    #    drags the lexer across upstream Perennial code that does use Notation,
    #    Program/Next Obligation and Fixpoint, which the raft corpus does not.
    checked = 0
    for root, _, files in os.walk(repo_root):
        if f"{os.sep}.git" in root:
            continue
        for fn in sorted(files):
            if not fn.endswith(".v"):
                continue
            p = os.path.join(root, fn)
            try:
                src = read_source(p)
            except OSError as exc:
                failures.append(f"unreadable: {p}: {exc}")
                continue
            segs = scan_segments(src)
            if "".join(src[a:b] for _, a, b in segs) != src:
                failures.append(f"round trip not exact: {p}")
            checked += 1
    print(f"round trip: {checked} .v files, byte exact")

    # 3. The hand-verified raft inventory.
    raft = os.path.join(repo_root, RAFT_DIR)
    counted = {}
    if os.path.isdir(raft):
        for p in collect_paths([raft]):
            units, _ = parse_file(p, read_source(p))
            base = os.path.basename(p)
            counted[base] = (
                len([u for u in units if u.kind == "assumed" and not u.is_obligation]),
                len([u for u in units if u.terminator == "Admitted"]),
                len([u for u in units if u.is_obligation]),
            )
            # A spec file declares exactly one function's triple and assumes
            # nothing.  This is the invariant the layout exists to enforce, and
            # checking it beats hard-coding a list of spec file names.
            if base.startswith("spec_"):
                n_ax, n_ad, n_ob = counted[base]
                if (n_ob, n_ax, n_ad) != (1, 0, 0):
                    failures.append(
                        f"{base}: a spec file must declare exactly one "
                        f"Parameter and assume nothing, got "
                        f"{n_ob} obligations / {n_ax} axioms / {n_ad} admitted"
                    )
        for base, want in EXPECTED_AXIOMS.items():
            got = counted.get(base, (None, None))[0]
            if got != want:
                failures.append(f"{base}: expected {want} axioms, got {got}")
        for base, want in EXPECTED_ADMITS.items():
            got = counted.get(base, (None, None))[1]
            if got != want:
                failures.append(f"{base}: expected {want} admitted, got {got}")
        tot_ax = sum(v[0] for v in counted.values())
        tot_ad = sum(v[1] for v in counted.values())
        tot_ob = sum(v[2] for v in counted.values())
        got_tot = {"axioms": tot_ax, "obligations": tot_ob, "admitted": tot_ad}
        for k, want in EXPECTED_TOTALS.items():
            if got_tot[k] != want:
                failures.append(f"raft total {k}: expected {want}, got {got_tot[k]}")
        print(
            f"raft inventory: {tot_ax} axioms, {tot_ad} admitted, "
            f"{tot_ob} module-type obligations (not trusted)"
        )
    else:
        failures.append(f"missing {RAFT_DIR}")

    if failures:
        for f_ in failures:
            print(f"FAIL: {f_}")
        return 1
    print("self-check OK")
    return 0


def main():
    import argparse

    repo_root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    parser = argparse.ArgumentParser(
        description="Render Rocq files down to their trust base: top-level "
        "theorem statements, the definitions they reach, and every axiom and "
        "admitted hole.  Proof bodies and proved helper lemmas are hidden.",
    )
    parser.add_argument("targets", nargs="*", help="`.v` files, directories, or -")
    parser.add_argument(
        "--root",
        action="append",
        default=[],
        metavar="NAME",
        help="treat NAME as a closure root (default: every Theorem and Corollary)",
    )
    parser.add_argument(
        "--summary", action="store_true", help="print only the trust-base report"
    )
    parser.add_argument(
        "--no-comments", action="store_true", help="strip comments as well as proofs"
    )
    parser.add_argument(
        "--self-check",
        action="store_true",
        help="verify the parser against the whole repo, then exit",
    )
    opts = parser.parse_args()

    if opts.self_check:
        return self_check(repo_root)
    if not opts.targets:
        parser.error("give at least one .v file or directory (or --self-check)")
    return run(opts)


if __name__ == "__main__":
    sys.exit(main())
