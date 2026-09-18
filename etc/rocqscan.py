"""Shallow scanning of Rocq sources, shared by the tools in etc/.

Nothing here parses Rocq.  It strips comments and string literals carefully
enough that the few things the tools do look at come out right:

  * where a sentence ends,
  * what a sentence declares, and inside which modules,
  * how a proof ended (``Qed``, ``Admitted``, ``Abort``),
  * which Go function a Hoare triple's program expression names.

That last one is the only part that knows a *toolchain* rather than Rocq:
Goose's rendering of a call and Perennial's ``{{{ … }}}`` triple notation.
Both are named in the constants below.

Known gaps, in the order they are likely to bite:

  * ``Notation`` and ``Ltac`` declare names this module does not index, so a
    reference through one is invisible;
  * a name is resolved by spelling, not by scope, so shadowing and ``Import``
    are not modelled;
  * a declaration inside a proof body (``Local Definition`` after ``Proof.``)
    would be read as a top-level one.

This is the part of the tooling most likely to rot, since it is the only part
that depends on how the development writes things down.  It has a self-test:
``python3 etc/rocqscan.py`` runs it, and so does
``etc/check-module-discipline.py --selftest``.
"""

import collections
import os
import re

# --------------------------------------------------------------------------
# Toolchain conventions.  Goose names a method's body
# <Recv><GOOSE_METHOD_SEP><method> with IMPL_SUFFIX appended, and gives a
# package-level name its qualified string as a `go_string`.

GOOSE_METHOD_SEP = "__"
IMPL_SUFFIX = "ⁱᵐᵖˡ"  # the superscript "impl" Goose appends


# --------------------------------------------------------------------------
# Sentences and comments

def strip_comments(text):
    """Replace (* ... *) comments with spaces, preserving every offset."""
    out = list(text)
    i, depth, n = 0, 0, len(text)
    while i < n:
        if text.startswith("(*", i):
            depth += 1
            out[i] = out[i + 1] = " "
            i += 2
        elif depth and text.startswith("*)", i):
            depth -= 1
            out[i] = out[i + 1] = " "
            i += 2
        elif depth:
            if text[i] != "\n":
                out[i] = " "
            i += 1
        else:
            i += 1
    return "".join(out)


def sentence_end(text, start):
    """Offset just past the '.' ending the Rocq sentence starting at `start`.

    A sentence ends at a '.' followed by whitespace or end of input.  Dots
    inside qualified names (``pkg.Type.t``) and inside string literals are
    not followed by whitespace, or are skipped over with the string.
    """
    i, n = start, len(text)
    while i < n:
        c = text[i]
        if c == '"':
            i += 1
            while i < n and text[i] != '"':
                i += 1
            i += 1
            continue
        if c == "." and (i + 1 >= n or text[i + 1] in " \t\r\n"):
            return i + 1
        i += 1
    return n


# --------------------------------------------------------------------------
# Declarations

DECL_RE = re.compile(
    r"""^[ \t]*
        (?:Local[ \t]+|Global[ \t]+|Program[ \t]+|\#\[[^\]]*\][ \t]*)*
        (?P<kind>Axiom|Parameter|Conjecture|Hypothesis
                |Lemma|Theorem|Corollary|Proposition|Fact|Remark
                |Definition|Instance|Example
                |Record|Inductive|CoInductive|Variant|Class|Structure
                |Fixpoint|CoFixpoint)
        [ \t]+(?P<name>[A-Za-z_][A-Za-z_0-9'’]*)
    """,
    re.VERBOSE | re.MULTILINE,
)

# What a declaration keyword means for trust.  An ASSUMPTION is believed
# without proof; a PROVABLE one comes with a proof script that either closes
# or does not; everything else (Definition, Record, ...) is a definition,
# which is trusted in the different sense that a reader has to read it.
ASSUMPTION_KINDS = {"Axiom", "Parameter", "Conjecture", "Hypothesis"}
PROVABLE_KINDS = {
    "Lemma",
    "Theorem",
    "Corollary",
    "Proposition",
    "Fact",
    "Remark",
    "Example",
    "Instance",
}
TYPE_KINDS = {"Record", "Inductive", "CoInductive", "Variant", "Class", "Structure"}

# How a proof ends.  `Abort` leaves nothing behind, so it is neither a proof
# nor an assumption; `Admitted` is an assumption with a statement.  Matched
# anywhere on a line, not just at the start of one, because the short proofs
# are written `Proof. solve_decision. Defined.`
TERMINATOR_ANY_RE = re.compile(r"\b(?P<how>Qed|Defined|Admitted|Abort)[ \t]*\.")

# A module or section opens; `Module X := F Y.` and `Module Type X := S.`
# instantiate instead, and have no `End`.
OPEN_RE = re.compile(
    r"^[ \t]*(?P<kw>Module|Section)[ \t]+(?P<ty>Type[ \t]+)?"
    r"(?P<name>[A-Za-z_][A-Za-z_0-9'’]*)",
    re.MULTILINE,
)
CLOSE_RE = re.compile(
    r"^[ \t]*End[ \t]+(?P<name>[A-Za-z_][A-Za-z_0-9'’]*)[ \t]*\.",
    re.MULTILINE,
)


def module_events(text):
    """[(offset, +1|-1, kind, name)] for the Module/Section structure.

    `kind` is "Module", "Module Type" or "Section".  An instantiation
    (``Module X := F Y.``) opens nothing and is skipped.
    """
    events = []
    for m in OPEN_RE.finditer(text):
        end = sentence_end(text, m.end())
        if ":=" in text[m.end() : end]:
            continue  # an instantiation, not a block
        kind = m.group("kw")
        if kind == "Module" and m.group("ty"):
            kind = "Module Type"
        events.append((m.start(), 1, kind, m.group("name")))
    for m in CLOSE_RE.finditer(text):
        events.append((m.start(), -1, None, m.group("name")))
    events.sort()
    return events


def module_stacks(text):
    """[(offset, stack)] where `stack` is the [(kind, name)] open at offset."""
    stacks, stack = [], []
    for off, delta, kind, name in module_events(text):
        if delta > 0:
            stack = stack + [(kind, name)]
        else:
            # Pop to and including `name`.  A stray `End` for something never
            # opened (a file scanned from the middle) pops nothing.  Rebuild
            # rather than mutate: earlier snapshots share this list.
            if any(n == name for _k, n in stack):
                cut = max(i for i, (_k, n) in enumerate(stack) if n == name)
                stack = stack[:cut]
        stacks.append((off, stack))
    return stacks


def _stack_at(stacks, offset):
    lo, hi, cur = 0, len(stacks) - 1, []
    while lo <= hi:
        mid = (lo + hi) // 2
        if stacks[mid][0] <= offset:
            cur = stacks[mid][1]
            lo = mid + 1
        else:
            hi = mid - 1
    return cur


# --------------------------------------------------------------------------
# Hoare triples and the Go functions they name

# A method call, `<recv> @! (go.PointerType <pkg>.<Type>) @! "<method>" #args`,
# or the value-receiver form without the PointerType wrapper.  The receiver
# expression may be anything, including a chain of field references.
METHOD_RE = re.compile(
    r"""@!\s*
        \(?\s*(?:go\.PointerType\s+)?
        (?P<pkg>[A-Za-z_][\w]*)\.(?P<typ>[A-Za-z_][\w]*)
        \s*\)?\s*@!\s*"(?P<meth>[^"]+)"
    """,
    re.VERBOSE,
)

# A package-level call, `@! <pkg>.<Fn> #args`.
FUNC_RE = re.compile(r"@!\s*(?P<pkg>[A-Za-z_][\w]*)\.(?P<fn>[A-Za-z_][\w]*)\s*#")

# A function reached through the semantics rather than by name, which is how
# an untranslated one has to be called: `#(functions <pkg>.<Fn> [...])`.
# A `go.<name>` there is a predeclared operation (`go.len`, ...), not a Go
# function of the program under verification.
FUNCTIONS_RE = re.compile(r"functions\s+(?P<pkg>[A-Za-z_][\w]*)\.(?P<fn>[A-Za-z_][\w]*)")

# Dynamic dispatch through an interface value: `#(methods i.(interface.ty) "Term" ...)`.
# The callee is whatever the client supplied, so this is an interface contract
# rather than a spec of a Go function.
IFACE_RE = re.compile(r"methods\s")


def go_refs(statement):
    """The Go functions a triple's program expression names.

    Returns (functions, iface) where `functions` is a list of canonical keys
    like ``pkg.Type.method`` or ``pkg.function``, and `iface` says whether
    the triple is about an interface method instead.
    """
    found = []
    text = statement
    for m in METHOD_RE.finditer(statement):
        found.append("{}.{}.{}".format(m.group("pkg"), m.group("typ"), m.group("meth")))
        # Blank the match so FUNC_RE cannot read the receiver type as a call.
        text = text[: m.start()] + " " * (m.end() - m.start()) + text[m.end() :]
    for m in FUNC_RE.finditer(text):
        found.append("{}.{}".format(m.group("pkg"), m.group("fn")))
    for m in FUNCTIONS_RE.finditer(text):
        if m.group("pkg") == "go":
            continue  # a predeclared builtin (go.len, ...), not a Go function
        found.append("{}.{}".format(m.group("pkg"), m.group("fn")))
    return sorted(set(found)), bool(IFACE_RE.search(statement)) and not found


def is_exported(go_fn):
    """Whether Go's capitalization rule exports the function `pkg.[Type.]fn`.

    The last component is the function or method name.  This is about the
    *name*: a method of an unexported type is reported exported, because the
    method is what a wrapper in the same package re-exports, which is how
    ``raft.raft.Step`` is reached from outside.
    """
    last = go_fn.split(".")[-1]
    return bool(last) and last[0].isupper()


# --------------------------------------------------------------------------
# Requires, for the file dependency graph

REQUIRE_RE = re.compile(
    r"^[ \t]*(?:From[ \t]+(?P<from>[\w.]+)[ \t]+)?Require[ \t]+"
    r"(?:Import[ \t]+|Export[ \t]+)?",
    re.MULTILINE,
)


def requires(text):
    """The logical paths a file requires, as dotted strings.

    ``From X Require Import a b.`` yields ``X.a`` and ``X.b``; a plain
    ``Require Export a.b c.d.`` yields them as written.
    """
    out = []
    for m in REQUIRE_RE.finditer(text):
        end = sentence_end(text, m.end())
        body = text[m.end() : end].rstrip()
        if body.endswith("."):
            body = body[:-1]
        prefix = m.group("from")
        for tok in body.split():
            if not tok or not tok[0].isalpha():
                continue
            out.append("{}.{}".format(prefix, tok) if prefix else tok)
    return out


# --------------------------------------------------------------------------
# The scan

Decl = collections.namedtuple(
    "Decl",
    "path line kind name statement is_triple go_fns iface "
    "modpath in_module_type ended ended_line start end lines refs proof_refs",
)


IDENT_RE = re.compile(r"[A-Za-z_][A-Za-z_0-9'’]*(?:\.[A-Za-z_][A-Za-z_0-9'’]*)*")

# Names introduced by a Record's fields or an Inductive's constructors, which
# a reader of the type has to read but which are not declarations of their own.
RECORD_FIELD_RE = re.compile(r"(?:\{|;)\s*(?P<name>[A-Za-z_][A-Za-z_0-9'’]*)\s*:[^=]")
CTOR_RE = re.compile(r"(?:\A|\||:=)\s*(?P<name>[A-Z_][A-Za-z_0-9'’]*)")


def sub_names(kind, statement):
    """The field or constructor names a type declaration brings with it."""
    if kind not in TYPE_KINDS:
        return []
    body = statement.split(":=", 1)[1] if ":=" in statement else statement
    if "{" in body:
        return sorted({m.group("name") for m in RECORD_FIELD_RE.finditer(body)})
    return sorted({m.group("name") for m in CTOR_RE.finditer(body)})


def scan_file(path, text=None):
    """Every declaration in a file, in source order."""
    if text is None:
        with open(path, encoding="utf-8", errors="replace") as f:
            text = f.read()
    raw = text
    text = strip_comments(raw)
    stacks = module_stacks(text)
    matches = list(DECL_RE.finditer(text))
    decls = []
    for i, m in enumerate(matches):
        end = sentence_end(text, m.end())
        statement = text[m.end() : end]
        is_triple = "{{{" in statement
        go_fns, iface = go_refs(statement) if is_triple else ([], False)
        stack = _stack_at(stacks, m.start())
        ended, ended_line, proof_refs = None, None, []
        if m.group("kind") in PROVABLE_KINDS:
            # The proof runs to the first terminator before the next
            # declaration.  A declaration with no proof at all (a Parameter-
            # like Instance) gets None.
            limit = matches[i + 1].start() if i + 1 < len(matches) else len(text)
            t = TERMINATOR_ANY_RE.search(text, end, limit)
            if t:
                ended = t.group("how")
                ended_line = raw.count("\n", 0, t.start()) + 1
                # What the proof script names.  Not part of what the
                # statement says, but it is how a lemma gets used, so it is
                # what tells a helper lemma from an unused one.
                proof_refs = sorted(set(IDENT_RE.findall(text[end : t.start()])))
        decls.append(
            Decl(
                path=path,
                line=raw.count("\n", 0, m.start()) + 1,
                kind=m.group("kind"),
                name=m.group("name"),
                statement=statement,
                is_triple=is_triple,
                go_fns=go_fns,
                iface=iface,
                modpath=tuple(n for k, n in stack if k != "Section"),
                in_module_type=any(k == "Module Type" for k, _n in stack),
                ended=ended,
                ended_line=ended_line,
                start=m.start(),
                end=end,
                lines=text.count("\n", m.start(), end) + 1,
                refs=sorted(set(IDENT_RE.findall(statement))),
                proof_refs=proof_refs,
            )
        )
    return decls


def qualified(decl):
    """The declaration's name with its enclosing modules, as Rocq writes it."""
    return ".".join(decl.modpath + (decl.name,))


def iter_files(root, suffix=".v"):
    for dirpath, _dirs, files in os.walk(root):
        for fn in sorted(files):
            if fn.endswith(suffix):
                yield os.path.join(dirpath, fn)


# --------------------------------------------------------------------------
# Self-test for the parsing contract.

SELFTEST_TRIPLES = [
    # a pointer-receiver method
    ('{{{ is_pkg_init raft }}} r @! (go.PointerType raft.raft) @! "poll" #from'
     ' {{{ RET #(); True }}}',
     ["raft.raft.poll"], False),
    # a receiver expression that is itself a chain of field refs
    ('{{{ True }}} (trk.[tracker.ProgressTracker.t, "Config"]'
     '.[tracker.Config.t, "Voters"]) @! (go.PointerType quorum.JointConfig)'
     ' @! "IDs" #() {{{ RET #(); True }}}',
     ["quorum.JointConfig.IDs"], False),
    # a package-level function
    ('{{{ True }}} @! raft.traceSendMessage #r #mp {{{ RET #(); True }}}',
     ["raft.traceSendMessage"], False),
    # an untranslated function reached through the semantics
    ('{{{ True }}} #(functions slices.Sort [go.SliceType go.uint64]) #data'
     ' {{{ RET #(); True }}}',
     ["slices.Sort"], False),
    # a predeclared builtin is not a Go function of the program
    ('{{{ True }}} #(functions go.len [tracker.ProgressMap]) #mref'
     ' {{{ RET #(W64 0); True }}}',
     [], False),
    # dispatch through a client-supplied interface value: a contract, not a
    # specification of a Go function under verification
    ('{{{ is_Logger l }}} #(methods l.(interface.ty) meth l.(interface.v))'
     ' #format {{{ RET #(); True }}}',
     [], True),
    # a model-level map operation is neither
    ('{{{ own_tracker cfg tv votes }}} map.lookup1 go.uint64'
     ' (go.PointerType tracker.Progress) #m #i {{{ RET #pr; True }}}',
     [], False),
]

SELFTEST_SOURCE = '''\
Require Export New.proof.a.b.
From New.proof Require Import c d.

Module role.
Inductive t := Follower | Candidate | Leader.
End role.

Module msg.
Record t := mk { ty : mtype.t ; from : w64 }.
End msg.

Module Type POLL.
  Parameter wp_poll : wp_poll_body.
End POLL.

Module PollProof (P : POLL_POSTULATES) : POLL.
  Axiom wp_poll : wp_poll_body.
End PollProof.

Module Poll := PollProof PollPostulates.

Section proof.
Lemma closed : P.
Proof. exact I. Qed.
Lemma open : Q.
Proof. (* Admitted. is quoted here *) idtac. Admitted. (* Trusted *)
Definition d := role.Leader.
End proof.
'''


def selftest():
    bad = []

    for stmt, want_fns, want_iface in SELFTEST_TRIPLES:
        got = go_refs(stmt)
        if got != (want_fns, want_iface):
            bad.append(
                "go_refs\n  in   {}\n  want {}\n  got  {}".format(
                    stmt, (want_fns, want_iface), got
                )
            )

    # A sentence ends at '.' followed by whitespace -- not at a dot inside a
    # qualified name, a record projection, or a string literal.
    text = 'Lemma f : rv.(pkg.Type.field\') = x /\\ s = "a.b c" . rest'
    got = text[: sentence_end(text, len("Lemma f :"))]
    if not got.endswith(" .") or "rest" in got:
        bad.append("sentence_end: {!r}".format(got))

    # Comments blank out to spaces: same length, newlines kept (so line
    # numbers survive), and nesting counted -- several doc comments in this
    # development hold a worked example inside (* ... *).
    src = "a(** x (* y *) z *)b\nc"
    out = strip_comments(src)
    if (len(out), out.count("\n"), out[0], out[-1]) != (len(src), 1, "a", "c"):
        bad.append("strip_comments shape: {!r}".format(out))
    if "x" in out or "y" in out or "z" in out:
        bad.append("strip_comments left comment text: {!r}".format(out))

    if is_exported("raft.raft.Step") is not True or is_exported("raft.raft.poll"):
        bad.append("is_exported")

    if requires(SELFTEST_SOURCE) != ["New.proof.a.b", "New.proof.c", "New.proof.d"]:
        bad.append("requires: {}".format(requires(SELFTEST_SOURCE)))

    scanned = scan_file("<selftest>", SELFTEST_SOURCE)
    decls = {d.name: d for d in scanned}
    by_kind = {(d.kind, d.name): d for d in scanned}
    checks = [
        # the module path, and Section not being part of it
        (by_kind[("Inductive", "t")].modpath == ("role",), "module path"),
        (by_kind[("Record", "t")].modpath == ("msg",), "module path (second)"),
        # a Parameter in a signature is an obligation, not an assumption
        (by_kind[("Parameter", "wp_poll")].in_module_type is True,
         "Parameter in Module Type"),
        # ... but the Axiom discharging it inside the functor is one
        (by_kind[("Axiom", "wp_poll")].in_module_type is False, "Axiom in functor"),
        # an instantiation opens no block, so `d` is not inside `Poll`
        (decls["d"].modpath == (), "instantiation does not nest"),
        (decls["closed"].ended == "Qed", "Qed detected"),
        # a name used only in a proof script is a use, and is kept apart
        # from the names the statement itself mentions
        (decls["closed"].proof_refs == ["I", "Proof", "exact"], "proof refs"),
        (decls["closed"].refs == ["P"], "statement refs"),
        # the quoted `Admitted.` in the comment does not close the proof early
        (decls["open"].ended == "Admitted", "Admitted detected"),
        # and the line it ends on is where a marker comment would sit
        ("Trusted" in SELFTEST_SOURCE.split("\n")[decls["open"].ended_line - 1],
         "Admitted line"),
    ]
    for ok, what in checks:
        if not ok:
            bad.append("scan_file: " + what)

    # A Record's fields and an Inductive's constructors come with the type.
    ctors = sub_names("Inductive", " := Follower | Candidate | Leader.")
    if ctors != ["Candidate", "Follower", "Leader"]:
        bad.append("sub_names ctors: {}".format(ctors))
    fields = sub_names("Record", " := mk { ty : mtype.t ; from : w64 }.")
    if fields != ["from", "ty"]:
        bad.append("sub_names fields: {}".format(fields))

    for b in bad:
        print("FAIL " + b)
    print("rocqscan selftest: {}".format(
        "{} failures".format(len(bad)) if bad else "ok"))
    return 1 if bad else 0


if __name__ == "__main__":
    import sys

    sys.exit(selftest())
