#!/usr/bin/env python3
"""Check the one-Go-function-per-module-collection discipline.

The etcd raft proof is meant to state every Hoare triple about a Go function
in its own collection of four files::

    spec_<X>.v        Definition wp_<X>_body + Module Type <X> with one Parameter
    postulates_<X>.v  Module Type <X>_POSTULATES, Including its callees
    proof_<X>.v       Module <X>Proof (P : <X>_POSTULATES) : <X>.
    link_<X>.v        the instantiation

so that a Go function has exactly one specification and nothing can bypass
it.  See notes/decisions.md, "One file per function, via Rocq's module
system".  The discipline covers unproven and axiomatized triples too: an
``Axiom`` about a Go function is still a specification of that function.

This script finds the triples that are *not* in that shape.  It works by
reading the program expression out of each triple rather than by trusting
lemma names, so a spec called ``wp_campaign_peer_ids`` is still recognised as
a spec of ``quorum.JointConfig.IDs``.

Usage::

    etc/check-module-discipline.py                     # whole raft proof
    etc/check-module-discipline.py --scope election    # just the election proof
    etc/check-module-discipline.py --scope raft --summary
    etc/check-module-discipline.py --format json
    etc/check-module-discipline.py --selftest          # the parsing contract

Exits non-zero when an *error* is flagged, so it can be used as a gate;
warnings, notes and info do not fail it.
"""

import argparse
import collections
import json
import os
import re
import sys

# --------------------------------------------------------------------------
# Where things live

PROOF_ROOT = "new/proof/go_etcd_io/raft"
CODE_ROOTS = ["new/code"]

SCOPES = {
    "raft": PROOF_ROOT,
    "election": os.path.join(PROOF_ROOT, "v3_proof/election"),
}

# --------------------------------------------------------------------------
# Rocq source scanning
#
# Nothing here parses Rocq.  It strips comments and string literals carefully
# enough that the two things we do look at -- where a sentence ends, and which
# Go function a sentence names -- come out right.

DECL_RE = re.compile(
    r"""^[ \t]*
        (?:Local[ \t]+|Global[ \t]+|\#\[[^\]]*\][ \t]*)*
        (?P<kind>Axiom|Parameter|Conjecture|Hypothesis
                |Lemma|Theorem|Corollary|Proposition|Fact|Remark
                |Definition|Instance|Example)
        [ \t]+(?P<name>[A-Za-z_][A-Za-z_0-9'’]*)
    """,
    re.VERBOSE | re.MULTILINE,
)

ASSUMPTION_KINDS = {"Axiom", "Parameter", "Conjecture", "Hypothesis"}
PROVABLE_KINDS = {
    "Lemma",
    "Theorem",
    "Corollary",
    "Proposition",
    "Fact",
    "Remark",
    "Example",
}


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
    inside qualified names (``raft.raft.t``) and inside string literals are
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


# A method call: `expr @! (go.PointerType raft.raft) @! "poll" #args`, or the
# value-receiver form without the PointerType wrapper.
METHOD_RE = re.compile(
    r"""@!\s*
        \(?\s*(?:go\.PointerType\s+)?
        (?P<pkg>[A-Za-z_][\w]*)\.(?P<typ>[A-Za-z_][\w]*)
        \s*\)?\s*@!\s*"(?P<meth>[^"]+)"
    """,
    re.VERBOSE,
)

# A package-level call: `@! raft.traceSendMessage #r #mp`.
FUNC_RE = re.compile(r"@!\s*(?P<pkg>[A-Za-z_][\w]*)\.(?P<fn>[A-Za-z_][\w]*)\s*#")

# An untranslated or builtin function reached through the semantics:
# `#(functions slices.Sort [...])`.  `go.<builtin>` is a predeclared
# operation, not a Go function of the program under verification.
FUNCTIONS_RE = re.compile(r"functions\s+(?P<pkg>[A-Za-z_][\w]*)\.(?P<fn>[A-Za-z_][\w]*)")

# Dynamic dispatch through an interface value: `#(methods i.(interface.ty) "Term" ...)`.
# The callee is whatever the client supplied, so this is an interface contract
# rather than a spec of a Go function.
IFACE_RE = re.compile(r"methods\s")


def go_refs(statement):
    """The Go functions a triple's program expression names.

    Returns (functions, iface) where `functions` is a list of canonical keys
    like ``raft.raft.poll`` (package.type.method) or ``raft.newReadOnly``
    (package.function), and `iface` says whether the triple is about an
    interface method instead.
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


Decl = collections.namedtuple(
    "Decl", "path line kind name statement is_triple go_fns iface"
)


def scan_file(path):
    with open(path, encoding="utf-8") as f:
        raw = f.read()
    text = strip_comments(raw)
    decls = []
    for m in DECL_RE.finditer(text):
        end = sentence_end(text, m.end())
        statement = text[m.end() : end]
        is_triple = "{{{" in statement
        go_fns, iface = go_refs(statement) if is_triple else ([], False)
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
            )
        )
    return decls


# --------------------------------------------------------------------------
# The Goose-generated code, used to tell a real Go function from a typo and to
# say whether it has a translated body at all.


def scan_code(roots):
    """Map Go function -> {'impl': bool, 'file': path}.

    Keyed by the last two components -- ``raft.poll`` for the method ``poll``
    on ``raft``, ``voteRespMsgType`` for a package-level function -- because
    the package *alias* a proof writes (``raft.raft.poll``) is a Rocq module
    name that does not appear in the generated file's path (the raft package
    is ``new/code/go_etcd_io/raft/v3.v``).  Method and function names are
    distinctive enough across these five packages that dropping the alias
    costs nothing and avoids resolving Rocq's module aliases.
    """
    known = {}
    impl_re = re.compile(r"^Definition\s+(?P<name>[A-Za-z_][\w]*)ⁱᵐᵖˡ\b", re.MULTILINE)
    method_re = re.compile(
        r"MethodUnfold\s+\(?(?:go\.PointerType\s+)?\(?(?P<typ>[A-Za-z_][\w]*)\)?\s*\)?"
        r'\s*"(?P<meth>[^"]+)"'
    )
    name_re = re.compile(
        r"^Definition\s+(?P<name>[A-Za-z_][\w]*)\s*(?:\{[^}]*\}\s*)*"
        r':\s*go_string\s*:=\s*"(?P<qual>[^"]*)"',
        re.MULTILINE,
    )
    for root in roots:
        for dirpath, _dirs, files in os.walk(root):
            for fn in files:
                if not fn.endswith(".v"):
                    continue
                path = os.path.join(dirpath, fn)
                with open(path, encoding="utf-8", errors="replace") as f:
                    body = f.read()
                impls = {m.group("name") for m in impl_re.finditer(body)}
                for name in impls:
                    key = name.replace("__", ".", 1)
                    known.setdefault(key, {"impl": True, "file": path})
                for m in method_re.finditer(body):
                    key = "{}.{}".format(m.group("typ"), m.group("meth"))
                    has = "{}__{}".format(m.group("typ"), m.group("meth")) in impls
                    entry = known.setdefault(key, {"impl": has, "file": path})
                    entry["impl"] = entry["impl"] or has
                for m in name_re.finditer(body):
                    known.setdefault(
                        m.group("name"), {"impl": m.group("name") in impls, "file": path}
                    )
    return known


def code_key(go_fn):
    """Drop the package alias from a canonical key, for lookup in `known`."""
    parts = go_fn.split(".")
    return ".".join(parts[1:]) if len(parts) == 3 else parts[-1]


# --------------------------------------------------------------------------
# File classification

ROLE_RE = re.compile(r"^(spec|postulates|proof|link)_(?P<x>.+)$")


def classify(path):
    """(role, collection) for a proof file; role is None for support files."""
    base = os.path.basename(path)[:-2]
    m = ROLE_RE.match(base)
    if not m:
        return None, base
    return base.split("_", 1)[0], m.group("x")


def owning_collection(coll, specs):
    """The collection a `proof_X_branch.v` helper file belongs to.

    `Step`'s branch lemmas live in proof_raft__Step_MsgVote_gt.v and friends.
    Each is proof structure inside the `raft__Step` collection -- no Module
    Type, no Parameter -- so they must not be counted as separate specs of
    `Step`.  Walk back along `_`-separated suffixes to the longest prefix that
    has a spec file.
    """
    parts = coll.split("_")
    while parts:
        cand = "_".join(parts)
        if cand in specs:
            return cand
        parts.pop()
    return coll


def suggest_name(key):
    """The collection name the naming convention would give a Go function.

    A method is named after its receiver type (``raftLog__lastIndex``); a
    package-level function of the raft package after itself
    (``voteRespMsgType``); one from another package keeps its package, since
    a bare ``Sort`` says nothing (``slices_Sort``).
    """
    parts = key.split(".")
    if len(parts) == 3:
        return "{}__{}".format(parts[1], parts[2])
    if parts[0] == "raft":
        return parts[1]
    return "{}_{}".format(parts[0], parts[1])


# --------------------------------------------------------------------------
# Checks

Finding = collections.namedtuple("Finding", "code path line severity message")


def check(scope_dir, root, known, all_proof_files):
    findings = []
    files = sorted(
        os.path.join(dp, fn)
        for dp, _d, fns in os.walk(scope_dir)
        for fn in fns
        if fn.endswith(".v")
    )

    # collection -> role -> path
    collections_seen = collections.defaultdict(dict)
    for path in all_proof_files:
        role, coll = classify(path)
        if role:
            collections_seen[coll][role] = path

    specs = {c for c, roles in collections_seen.items() if "spec" in roles}

    # Go function -> list of (decl, role, collection)
    specs_by_fn = collections.defaultdict(list)
    triples = []

    for path in files:
        rel = os.path.relpath(path, root)
        role, coll = classify(path)
        for d in scan_file(path):
            if not d.is_triple:
                continue
            if d.kind == "Definition" and not d.name.endswith("_body"):
                # A predicate that bundles triples (is_Storage, a closure's
                # caller invariant).  Not a specification of a Go function.
                continue
            if not d.go_fns:
                if d.iface:
                    findings.append(
                        Finding(
                            "I-iface",
                            rel,
                            d.line,
                            "info",
                            "{} {} is an interface-method contract, not a Go "
                            "function spec; it belongs with its predicate".format(
                                d.kind, d.name
                            ),
                        )
                    )
                continue
            owner = owning_collection(coll, specs) if role == "proof" else coll
            triples.append((path, rel, role, owner, d))
            for key in d.go_fns:
                specs_by_fn[key].append((rel, d, role, owner))

    # --- F1: a triple about a Go function outside the spec/proof shape
    for path, rel, role, coll, d in triples:
        if role in ("spec", "proof"):
            continue
        base = os.path.basename(path)
        kind = "axiom" if d.kind in ASSUMPTION_KINDS else "lemma"
        findings.append(
            Finding(
                "F1-out-of-place",
                rel,
                d.line,
                "error",
                "{} {} specifies {} but {} is not a spec_*/proof_* file; "
                "give {} its own spec/postulates/proof/link collection "
                "(suggested name {})".format(
                    kind,
                    d.name,
                    ", ".join(d.go_fns),
                    base,
                    d.go_fns[0],
                    suggest_name(d.go_fns[0]),
                ),
            )
        )

    # --- F2: one Go function specified in more than one place
    for key, entries in sorted(specs_by_fn.items()):
        # A spec_X.v `_body` and the proof_X.v `Lemma` that discharges it are
        # one specification, so collapse a collection's spec+proof pair.
        places = {}
        for rel, d, role, coll in entries:
            slot = coll if role in ("spec", "proof") else "{}:{}".format(rel, d.name)
            places.setdefault(slot, []).append((rel, d))
        if len(places) > 1:
            where = "; ".join(
                "{}:{} ({})".format(rel, d.line, d.name)
                for entries2 in places.values()
                for rel, d in entries2
            )
            first = entries[0]
            findings.append(
                Finding(
                    "F2-duplicate-spec",
                    first[0],
                    first[1].line,
                    "error",
                    "{} has {} separate Hoare triples: {}. One Go function gets "
                    "one spec; if it seems to want two, look harder".format(
                        key, len(places), where
                    ),
                )
            )

    # --- F3: spec file shape
    for path in files:
        role, coll = classify(path)
        if role != "spec":
            continue
        rel = os.path.relpath(path, root)
        decls = scan_file(path)
        params = [d for d in decls if d.kind in ASSUMPTION_KINDS]
        with open(path, encoding="utf-8") as f:
            src = strip_comments(f.read())
        n_types = len(re.findall(r"^Module Type\b", src, re.MULTILINE))
        if n_types != 1:
            findings.append(
                Finding(
                    "F3-spec-shape",
                    rel,
                    1,
                    "error",
                    "spec file declares {} Module Types, expected exactly 1".format(
                        n_types
                    ),
                )
            )
        if len(params) != 1:
            findings.append(
                Finding(
                    "F3-spec-shape",
                    rel,
                    1,
                    "error",
                    "spec file declares {} Parameters ({}), expected exactly 1".format(
                        len(params), ", ".join(d.name for d in params) or "none"
                    ),
                )
            )
        proved = [d for d in decls if d.kind in PROVABLE_KINDS]
        if proved:
            findings.append(
                Finding(
                    "F3-spec-shape",
                    rel,
                    proved[0].line,
                    "error",
                    "spec file proves {}; a spec file states, it does not prove".format(
                        ", ".join(d.name for d in proved)
                    ),
                )
            )

    # --- F4: an incomplete collection
    for coll, roles in sorted(collections_seen.items()):
        if not any(
            os.path.relpath(p, root).startswith(os.path.relpath(scope_dir, root))
            for p in roles.values()
        ):
            continue
        missing = [r for r in ("spec", "postulates", "proof", "link") if r not in roles]
        if missing and "spec" in roles:
            findings.append(
                Finding(
                    "F4-incomplete",
                    os.path.relpath(roles["spec"], root),
                    1,
                    "error",
                    "collection {} is missing {}".format(coll, ", ".join(missing)),
                )
            )

    # --- F5: a proof file verifying a second Go function
    for path, rel, role, coll, d in triples:
        if role != "proof":
            continue
        own = collections_seen.get(coll, {}).get("spec")
        if own is None:
            # A branch helper such as proof_raft__Step_MsgVote_gt.v.
            continue
        spec_fns = set()
        for sd in scan_file(own):
            spec_fns.update(sd.go_fns)
        stray = [k for k in d.go_fns if k not in spec_fns]
        if stray:
            findings.append(
                Finding(
                    "F5-proof-leak",
                    rel,
                    d.line,
                    "error",
                    "{} in collection {} states a triple about {}, which is not "
                    "what {} specifies".format(
                        d.name, coll, ", ".join(stray), os.path.basename(own)
                    ),
                )
            )

    # --- F6: a spec whose Go function has no translated body
    for key, entries in sorted(specs_by_fn.items()):
        ck = code_key(key)
        if ck in known:
            if not known[ck]["impl"]:
                rel, d = entries[0][0], entries[0][1]
                findings.append(
                    Finding(
                        "I-untranslated",
                        rel,
                        d.line,
                        "info",
                        "{} is declared in the generated code but has no "
                        "translated body, so this triple can only be assumed".format(
                            key
                        ),
                    )
                )
        else:
            rel, d = entries[0][0], entries[0][1]
            findings.append(
                Finding(
                    "F6-unknown-function",
                    rel,
                    d.line,
                    "warning",
                    "{} names {}, which is in no generated package under {} -- "
                    "check the receiver type and method name".format(
                        d.name, key, ", ".join(CODE_ROOTS)
                    ),
                )
            )

    # --- N1: collection named after a different function than it specifies
    for path in files:
        role, coll = classify(path)
        if role != "spec":
            continue
        rel = os.path.relpath(path, root)
        for d in scan_file(path):
            if not d.go_fns or not d.name.endswith("_body"):
                continue
            want = suggest_name(d.go_fns[0])
            if want != coll:
                findings.append(
                    Finding(
                        "N1-name",
                        rel,
                        d.line,
                        "note",
                        "collection is called {} but specifies {} (convention "
                        "would name it {})".format(coll, d.go_fns[0], want),
                    )
                )

    return findings, specs_by_fn, collections_seen


# --------------------------------------------------------------------------

# --------------------------------------------------------------------------
# Self-test for the parsing contract, which is the part of this script most
# likely to rot: it is the only thing that depends on how Goose renders a call
# and on how this development writes a Hoare triple.  Run with --selftest.

SELFTEST_CASES = [
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


def selftest():
    bad = []

    for stmt, want_fns, want_iface in SELFTEST_CASES:
        got = go_refs(stmt)
        if got != (want_fns, want_iface):
            bad.append(
                "go_refs\n  in   {}\n  want {}\n  got  {}".format(
                    stmt, (want_fns, want_iface), got
                )
            )

    # A sentence ends at '.' followed by whitespace -- not at a dot inside a
    # qualified name, a record projection, or a string literal.
    text = 'Lemma f : rv.(raft.raft.trk\') = x /\\ s = "a.b c" . rest'
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

    for key, want in (
        ("raft.raftLog.lastIndex", "raftLog__lastIndex"),
        ("raft.voteRespMsgType", "voteRespMsgType"),
        ("slices.Sort", "slices_Sort"),
        ("tracker.NewInflights", "tracker_NewInflights"),
    ):
        if suggest_name(key) != want:
            bad.append(
                "suggest_name {} -> {} (want {})".format(key, suggest_name(key), want)
            )

    for key, want in (
        ("raft.raftLog.lastIndex", "raftLog.lastIndex"),
        ("raft.voteRespMsgType", "voteRespMsgType"),
    ):
        if code_key(key) != want:
            bad.append("code_key {} -> {}".format(key, code_key(key)))

    for b in bad:
        print("FAIL " + b)
    print("selftest: {}".format("{} failures".format(len(bad)) if bad else "ok"))
    return 1 if bad else 0


SEVERITY_ORDER = {"error": 0, "warning": 1, "note": 2, "info": 3}


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument(
        "--root",
        default=".",
        help="repository root (default: the current directory)",
    )
    ap.add_argument(
        "--scope",
        default="raft",
        help="raft, election, or a path under the repository root",
    )
    ap.add_argument("--format", choices=["text", "json"], default="text")
    ap.add_argument(
        "--severity",
        choices=["error", "warning", "note", "info"],
        default="note",
        help="lowest severity to report (default: note)",
    )
    ap.add_argument(
        "--summary", action="store_true", help="also print the Go function inventory"
    )
    ap.add_argument(
        "--selftest",
        action="store_true",
        help="check the expression-parsing contract and exit",
    )
    args = ap.parse_args()

    if args.selftest:
        return selftest()

    root = os.path.abspath(args.root)
    scope_dir = os.path.join(root, SCOPES.get(args.scope, args.scope))
    if not os.path.isdir(scope_dir):
        sys.exit("no such directory: {}".format(scope_dir))

    known = scan_code([os.path.join(root, c) for c in CODE_ROOTS])
    all_proof_files = sorted(
        os.path.join(dp, fn)
        for dp, _d, fns in os.walk(os.path.join(root, PROOF_ROOT))
        for fn in fns
        if fn.endswith(".v")
    )

    findings, specs_by_fn, _colls = check(scope_dir, root, known, all_proof_files)
    cutoff = SEVERITY_ORDER[args.severity]
    findings = [f for f in findings if SEVERITY_ORDER[f.severity] <= cutoff]
    findings.sort(key=lambda f: (SEVERITY_ORDER[f.severity], f.path, f.line))

    if args.format == "json":
        print(json.dumps([f._asdict() for f in findings], indent=2))
    else:
        by_file = collections.defaultdict(list)
        for f in findings:
            by_file[f.path].append(f)
        for path in sorted(by_file):
            print(path)
            for f in by_file[path]:
                print(
                    "  {}:{} {}: {}".format(f.line, f.severity, f.code, f.message)
                )
            print()
        counts = collections.Counter(f.severity for f in findings)
        print(
            "{} findings in {} files ({})".format(
                len(findings),
                len(by_file),
                ", ".join(
                    "{} {}".format(n, s) for s, n in sorted(counts.items())
                )
                or "none",
            )
        )
        if args.summary:
            print("\nGo functions with a Hoare triple in {}:".format(args.scope))
            for key in sorted(specs_by_fn):
                places = ", ".join(
                    "{}:{}".format(rel, d.line) for rel, d, _r, _c in specs_by_fn[key]
                )
                print("  {:50s} {}".format(key, places))

    return 1 if any(f.severity == "error" for f in findings) else 0


if __name__ == "__main__":
    sys.exit(main())
