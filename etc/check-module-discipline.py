#!/usr/bin/env python3
"""Check the one-Go-function-per-module-collection discipline.

A development following it states every Hoare triple about a Go function in
its own collection of four files::

    spec_<X>.v        Definition wp_<X>_body + Module Type <X> with one Parameter
    postulates_<X>.v  Module Type <X>_POSTULATES, Including its callees
    proof_<X>.v       Module <X>Proof (P : <X>_POSTULATES) : <X>.
    link_<X>.v        the instantiation

so that a Go function has exactly one specification and nothing can bypass
it.  See notes/decisions.md, "One file per function, via Rocq's module
system".  The discipline covers unproven and axiomatized triples too: an
``Axiom`` about a Go function is still a specification of that function.

When one function's proof needs several files, the extra ones go in a
per-function directory, so that listing the top level shows exactly the four
files of each collection:

    proof_<X>_helpers/*.v   internal lemmas -- no Module Type, no Parameter,
                            and only proof_<X>.v (or another helper) may
                            Require one

This script finds the triples that are *not* in that shape.  It works by
reading the program expression out of each triple rather than by trusting
lemma names, so a lemma whose name says nothing about its subject -- or says
the wrong thing -- is still attributed to the Go function it really
specifies.

Nothing here knows any particular package, function or file name.  What it
does assume is the *toolchain*: Goose's rendering of a call, Perennial's
``{{{ … }}}`` triple notation, and the file-naming convention above, all of
which are named in the constants below.  Point it at another development
with --proof-root.

Usage::

    etc/check-module-discipline.py                    # the default proof root
    etc/check-module-discipline.py --scope election_proof   # one directory of it
    etc/check-module-discipline.py --summary
    etc/check-module-discipline.py --format json
    etc/check-module-discipline.py --selftest         # the parsing contract

--scope takes a path, or the bare name of a directory anywhere under the
proof root.  Exits non-zero when an *error* is flagged, so it can be used as
a gate; warnings, notes and info do not fail it.
"""

import argparse
import collections
import json
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import rocqscan
from rocqscan import (
    ASSUMPTION_KINDS,
    GOOSE_METHOD_SEP,
    IMPL_SUFFIX,
    PROVABLE_KINDS,
    scan_file,
    strip_comments,
)

# --------------------------------------------------------------------------
# Defaults and conventions.  These are the only place anything about a
# particular repository layout is written down; all are overridable or are
# conventions of the layout itself rather than of one development.

# The development to check.  Any directory tree using the collection layout
# will do; this is just where this repository keeps the one that does.
DEFAULT_PROOF_ROOT = "new/proof/go_etcd_io/raft"

# Where the Goose output lives, used to confirm a spec names a real Go
# function and to say whether that function has a translated body.
DEFAULT_CODE_ROOTS = ["new/code"]

# The four file kinds of a collection, and the directory a function's extra
# proof files go in when its proof needs more than one.
ROLES = ("spec", "postulates", "proof", "link")
HELPERS_SUFFIX = "_helpers"

# A spec states its triple as `Definition wp_<fn><BODY_SUFFIX> := ∀ …` so that
# the binder list exists once; the Module Type's Parameter refers to it.
BODY_SUFFIX = "_body"

# How a collection is named after the Go function it specifies: a method as
# <Type><METHOD_SEP><method>, a package-level function as <fn>, either
# optionally prefixed with <pkg><PKG_SEP>.
METHOD_SEP = "__"
PKG_SEP = "_"

# GOOSE_METHOD_SEP is the same spelling as METHOD_SEP today, and a different
# thing: that one is how this development names a collection, this one is how
# Goose names a method's body.  Both live in rocqscan.

# --------------------------------------------------------------------------
# Scanning is rocqscan's job: how a sentence ends, what it declares, and
# which Go function a triple's program expression names.  That is the
# parsing contract shared with etc/tcb-report.py, and it has its own
# self-test.  What is left here is the layout of a collection.


# --------------------------------------------------------------------------
# The Goose-generated code, used to tell a real Go function from a typo and to
# say whether it has a translated body at all.


def scan_code(roots):
    """Index the Goose output.

    Returns (by_alias, by_local).  A proof writes a call as
    ``<alias>.<Type>.<method>`` or ``<alias>.<fn>``, where ``<alias>`` is a
    Rocq module name that need not match the generated file's path -- a
    package may be translated to ``<anything>.v`` and open ``Module foo.``
    inside it.  So the index is keyed twice: by (alias, local name), resolved
    through the ``Module`` declarations each generated file makes, and by
    local name alone as a fallback for an alias introduced some other way
    (a `Module Import`, a notation).  Local names are ``Type.method`` and
    bare ``fn``.
    """
    by_alias = collections.defaultdict(dict)
    by_local = {}
    alias_re = re.compile(r"^Module\s+(?P<name>[A-Za-z_][\w]*)\s*\.", re.MULTILINE)
    impl_re = re.compile(
        r"^Definition\s+(?P<name>[A-Za-z_][\w]*)" + re.escape(IMPL_SUFFIX) + r"\b",
        re.MULTILINE,
    )
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
                local = {}
                for name in impls:
                    local.setdefault(
                        name.replace(GOOSE_METHOD_SEP, ".", 1),
                        {"impl": True, "file": path},
                    )
                for m in method_re.finditer(body):
                    key = "{}.{}".format(m.group("typ"), m.group("meth"))
                    has = (
                        "{}{}{}".format(
                            m.group("typ"), GOOSE_METHOD_SEP, m.group("meth")
                        )
                        in impls
                    )
                    entry = local.setdefault(key, {"impl": has, "file": path})
                    entry["impl"] = entry["impl"] or has
                for m in name_re.finditer(body):
                    local.setdefault(
                        m.group("name"),
                        {"impl": m.group("name") in impls, "file": path},
                    )
                aliases = {m.group("name") for m in alias_re.finditer(body)}
                for alias in aliases:
                    by_alias[alias].update(local)
                for key, entry in local.items():
                    by_local.setdefault(key, entry)
    return dict(by_alias), by_local


def lookup_code(go_fn, index):
    """The generated-code entry for a Go function key, or None.

    Tries the alias the proof wrote first, then the local name alone.
    """
    by_alias, by_local = index
    parts = go_fn.split(".")
    alias, local = parts[0], ".".join(parts[1:])
    entry = by_alias.get(alias, {}).get(local)
    return entry if entry is not None else by_local.get(local)


# --------------------------------------------------------------------------
# File classification

ROLE_RE = re.compile(r"^(?P<role>{})_(?P<x>.+)$".format("|".join(ROLES)))
HELPERS_RE = re.compile(rf"^proof_(?P<x>.+){re.escape(HELPERS_SUFFIX)}$")


def classify(path):
    """(role, collection) for a proof file.

    Roles are the four file kinds of a collection, plus "helper" for a file
    inside ``proof_<fn><HELPERS_SUFFIX>/``.  A helper is proof structure --
    an internal lemma split out so that `make -j` can check it in parallel --
    not a specification, so it is allowed to state triples about its function
    and must not declare a Module Type.  Anything else -- shared predicates,
    pure lemmas, tactics -- gets role None and is only checked for triples it
    should not be holding.
    """
    base = os.path.basename(path)[:-2]
    hm = HELPERS_RE.match(os.path.basename(os.path.dirname(path)))
    if hm:
        return "helper", hm.group("x")
    m = ROLE_RE.match(base)
    if not m:
        return None, base
    return m.group("role"), m.group("x")


def owning_collection(coll, specs):
    """The collection a `proof_<X>_<suffix>.v` file belongs to.

    Such a file is proof structure inside collection `<X>` -- no Module Type,
    no Parameter -- so it must not be counted as a separate spec of `<X>`'s
    function.  Walk back along `_`-separated suffixes to the longest prefix
    that has a spec file.  Used for a helper that has not been moved into
    the helpers directory yet, which is what H1 reports.
    """
    parts = coll.split("_")
    while parts:
        cand = "_".join(parts)
        if cand in specs:
            return cand
        parts.pop()
    return coll


def acceptable_names(key):
    """The collection names the naming convention allows for a Go function.

    Preferred first.  A method is named after its receiver type and method
    (``Type__method``); a package-level function after itself (``fn``).
    Either may be prefixed with the package, which is what you want when a
    bare method or function name would say nothing on its own -- so both
    ``Sort`` and ``slices_Sort`` are accepted for ``slices.Sort``.

    Deliberately a set and not one answer: which of the two reads better
    depends on the package, and picking for the author would mean this script
    knowing which package is "the" one under verification.
    """
    parts = key.split(".")
    pkg = parts[0]
    if len(parts) == 3:
        bare = f"{parts[1]}{METHOD_SEP}{parts[2]}"
    else:
        bare = parts[1]
    return (bare, f"{pkg}{PKG_SEP}{bare}")


def suggest_name(key):
    """The preferred collection name, for a message."""
    return acceptable_names(key)[0]


# --------------------------------------------------------------------------
# Checks

Finding = collections.namedtuple("Finding", "code path line severity message")


def check(scope_dir, root, code_index, code_roots, all_proof_files):
    findings = []
    files = sorted(
        os.path.join(dp, fn)
        for dp, _d, fns in os.walk(scope_dir)
        for fn in fns
        if fn.endswith(".v")
    )

    # collection -> role -> path (helpers are a list; there can be many)
    collections_seen = collections.defaultdict(dict)
    helpers_of = collections.defaultdict(list)
    for path in all_proof_files:
        role, coll = classify(path)
        if role == "helper":
            helpers_of[coll].append(path)
        elif role:
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
            if d.kind == "Definition" and not d.name.endswith(BODY_SUFFIX):
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
                            f"{d.kind} {d.name} is an interface-method contract, not a Go "
                            "function spec; it belongs with its predicate",
                        )
                    )
                continue
            owner = owning_collection(coll, specs) if role == "proof" else coll
            triples.append((path, rel, role, owner, d))
            for key in d.go_fns:
                specs_by_fn[key].append((rel, d, role, owner))

    # --- F1: a triple about a Go function outside the spec/proof shape
    for path, rel, role, coll, d in triples:
        if role in ("spec", "proof", "helper"):
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
            slot = coll if role in ("spec", "proof", "helper") else f"{rel}:{d.name}"
            places.setdefault(slot, []).append((rel, d))
        if len(places) > 1:
            where = "; ".join(
                f"{rel}:{d.line} ({d.name})"
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
                    f"{key} has {len(places)} separate Hoare triples: {where}. One Go function gets "
                    "one spec; if it seems to want two, look harder",
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
                    f"spec file declares {n_types} Module Types, expected exactly 1",
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
        entry = lookup_code(key, code_index)
        if entry is not None:
            if not entry["impl"]:
                rel, d = entries[0][0], entries[0][1]
                findings.append(
                    Finding(
                        "I-untranslated",
                        rel,
                        d.line,
                        "info",
                        f"{key} is declared in the generated code but has no "
                        "translated body, so this triple can only be assumed",
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
                        d.name, key, ", ".join(code_roots)
                    ),
                )
            )

    # --- H1: a proof helper sitting at the top level.  When one function's
    # proof needs several files, the extra ones go in proof_<fn>_helpers/ so
    # that the top-level directory shows exactly the four files of each
    # collection and is auditable by listing it.
    specs_set = {c for c, roles in collections_seen.items() if "spec" in roles}
    for path in files:
        role, coll = classify(path)
        if role != "proof" or coll in specs_set:
            continue
        owner = owning_collection(coll, specs_set)
        if owner == coll:
            continue  # not a helper of anything; F4 will complain instead
        findings.append(
            Finding(
                "H1-helper-at-top-level",
                os.path.relpath(path, root),
                1,
                "error",
                f"this is a proof helper of {owner}, not a collection of its own; "
                f"move it to proof_{owner}_helpers/ so the top level keeps four "
                "files per Go function",
            )
        )

    # --- H2: a helpers directory holds proof structure, never a spec
    for coll, paths in sorted(helpers_of.items()):
        for path in paths:
            rel = os.path.relpath(path, root)
            with open(path, encoding="utf-8") as f:
                src = strip_comments(f.read())
            if re.search(r"^Module Type\b", src, re.MULTILINE):
                findings.append(
                    Finding(
                        "H2-helper-declares-spec",
                        rel,
                        1,
                        "error",
                        f"a file under proof_{coll}_helpers/ declares a Module Type; "
                        "a helper is proof structure, so if this is really a "
                        "specification it needs a collection of its own",
                    )
                )
            for d in scan_file(path):
                if d.kind in ASSUMPTION_KINDS:
                    findings.append(
                        Finding(
                            "H2-helper-declares-spec",
                            rel,
                            d.line,
                            "error",
                            f"{d.kind} {d.name} is an assumption inside proof_{coll}_helpers/; "
                            "an axiom about a Go function belongs in that "
                            "function's own collection",
                        )
                    )

    # --- H3: a helpers directory with no collection to help
    for coll in sorted(helpers_of):
        if "proof" not in collections_seen.get(coll, {}):
            findings.append(
                Finding(
                    "H3-orphan-helpers",
                    os.path.relpath(helpers_of[coll][0], root),
                    1,
                    "error",
                    f"proof_{coll}_helpers/ has no proof_{coll}.v to help",
                )
            )

    # --- N1: collection named after a different function than it specifies
    for path in files:
        role, coll = classify(path)
        if role != "spec":
            continue
        rel = os.path.relpath(path, root)
        for d in scan_file(path):
            if not d.go_fns or not d.name.endswith(BODY_SUFFIX):
                continue
            allowed = acceptable_names(d.go_fns[0])
            if coll not in allowed:
                findings.append(
                    Finding(
                        "N1-name",
                        rel,
                        d.line,
                        "note",
                        "collection is called {} but specifies {} (convention "
                        "would name it {})".format(
                            coll, d.go_fns[0], " or ".join(allowed)
                        ),
                    )
                )

    return findings, specs_by_fn, collections_seen, helpers_of


# --------------------------------------------------------------------------

# --------------------------------------------------------------------------
# Self-test.  The parsing contract -- how a sentence ends, how Goose renders
# a call, how this development writes a Hoare triple -- is rocqscan's, and
# is tested there; run with --selftest and both run.  What is tested here is
# the collection layout this script adds on top.


def selftest():
    bad = []
    rc = rocqscan.selftest()

    # The naming convention accepts a bare name or a package-prefixed one;
    # nothing here decides which package is "the" one being verified.
    for key, want in (
        ("pkg.Type.method", ("Type__method", "pkg_Type__method")),
        ("pkg.fn", ("fn", "pkg_fn")),
    ):
        got = acceptable_names(key)
        if got != want:
            bad.append(f"acceptable_names {key} -> {got} (want {want})")

    # The code index resolves the alias a proof writes against the `Module`
    # declarations of the generated file, and falls back to the bare name.
    index = (
        {"alias": {"Type.method": {"impl": True, "file": "x.v"}}},
        {"other.thing": {"impl": False, "file": "y.v"}},
    )
    for key, want in (
        ("alias.Type.method", True),
        ("nosuch.other.thing", False),
        ("alias.no.such", None),
    ):
        entry = lookup_code(key, index)
        got = None if entry is None else entry["impl"]
        if got != want:
            bad.append(f"lookup_code {key} -> {got} (want {want})")

    for b in bad:
        print("FAIL " + b)
    print("selftest: {}".format(f"{len(bad)} failures" if bad else "ok"))
    return 1 if (bad or rc) else 0


def resolve_scope(scope, proof_root):
    """The directory to report on: all of the proof root, a path, or a name.

    Taking a bare directory name and finding it under the proof root is the
    convenience that a hardcoded table of scope names used to provide.
    """
    if not scope:
        return proof_root
    for cand in (scope, os.path.join(proof_root, scope)):
        if os.path.isdir(cand):
            return os.path.abspath(cand)
    matches = sorted(
        dp
        for dp, _dirs, _f in os.walk(proof_root)
        for d in [os.path.basename(dp)]
        if d == scope
    )
    if len(matches) == 1:
        return matches[0]
    if not matches:
        sys.exit(f"no directory named {scope!r} under {proof_root} (and no such path)")
    sys.exit(
        "{!r} is ambiguous under {}:\n  {}".format(
            scope, proof_root, "\n  ".join(matches)
        )
    )


SEVERITY_ORDER = {"error": 0, "warning": 1, "note": 2, "info": 3}


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument(
        "--root",
        default=".",
        help="repository root (default: the current directory)",
    )
    ap.add_argument(
        "--proof-root",
        default=DEFAULT_PROOF_ROOT,
        help=f"the development to check, relative to --root (default: {DEFAULT_PROOF_ROOT})",
    )
    ap.add_argument(
        "--code-root",
        action="append",
        dest="code_roots",
        metavar="DIR",
        help="where the generated Go translation lives, relative to --root; "
        "repeatable (default: {})".format(" ".join(DEFAULT_CODE_ROOTS)),
    )
    ap.add_argument(
        "--scope",
        default=None,
        help="restrict the report to a path, or to the bare name of a "
        "directory anywhere under the proof root (default: all of it)",
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
    proof_root = os.path.join(root, args.proof_root)
    if not os.path.isdir(proof_root):
        sys.exit(f"no such proof root: {proof_root}")
    code_roots = args.code_roots or DEFAULT_CODE_ROOTS

    scope_dir = resolve_scope(args.scope, proof_root)

    code_index = scan_code([os.path.join(root, c) for c in code_roots])
    all_proof_files = sorted(
        os.path.join(dp, fn)
        for dp, _d, fns in os.walk(proof_root)
        for fn in fns
        if fn.endswith(".v")
    )

    findings, specs_by_fn, _colls, _helpers = check(
        scope_dir, root, code_index, code_roots, all_proof_files
    )
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
                print(f"  {f.line}:{f.severity} {f.code}: {f.message}")
            print()
        counts = collections.Counter(f.severity for f in findings)
        print(
            "{} findings in {} files ({})".format(
                len(findings),
                len(by_file),
                ", ".join(f"{n} {s}" for s, n in sorted(counts.items())) or "none",
            )
        )
        if args.summary:
            multi = {c: v for c, v in sorted(_helpers.items()) if v}
            if multi:
                print("Functions whose proof spans several files:")
                for coll, paths in multi.items():
                    print(f"  {coll:34s} proof_{coll}_helpers/ ({len(paths)} files)")
                print()
            print(f"Go functions with a Hoare triple in {args.scope}:")
            for key in sorted(specs_by_fn):
                places = ", ".join(
                    f"{rel}:{d.line}" for rel, d, _r, _c in specs_by_fn[key]
                )
                print(f"  {key:50s} {places}")

    return 1 if any(f.severity == "error" for f in findings) else 0


if __name__ == "__main__":
    sys.exit(main())
