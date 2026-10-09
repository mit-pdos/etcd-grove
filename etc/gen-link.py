#!/usr/bin/env python3
"""Generate Proof/go_etcd_io/raft/v3/Link.lean from the Rocq link structure.

Each Rocq collection <fn> has spec_<fn>.v (`Module Type NAME.`), postulates_<fn>.v
(`Include CALLEE.` for each callee, in order) and link_<fn>.v (the functor applied to
the callees' results). In Lean the result of <fn> is its `wp_proof` applied to the
callees' results, in the postulates' order:

    theorem <T>.wp_<M> : <T>.<M>.spec (GF := GF) (hG := hG) := <T>.<M>.wp_proof <callees>

Functions with no Rocq counterpart (Lean-first: the `confchange` package, translated
and proved here on 2026-10-08) are listed in etc/link-lean-first.txt, one per line as
`<fn>: <callee> <callee> ...` (the callees in the order of the `wp_proof`'s
hypotheses), and linked the same way; a Rocq-side function listed there has its
callees overridden (a Rocq `Axiom` proved here).

The Spec/Proof files of a function are found by its name: `Spec/<pkg>/<fn>.lean`, or
`Spec/<pkg>/<f>.lean` for a name `<last component of pkg>_<f>` (tracker_NewInflights:
Spec/go_etcd_io/raft/v3/tracker/NewInflights.lean).

usage: etc/gen-link.py ROCQ_PROOF_DIR > Proof/go_etcd_io/raft/v3/Link.lean
       etc/gen-link.py --cache > Proof/go_etcd_io/etcd/cache/v3/Link.lean

`--cache` links the proofs of etcd's `cache` package (`Proof/go_etcd_io/etcd/cache/v3/` and
the specs and proofs of its functions), which are all
Lean-first: they are read from etc/link-lean-first-cache.txt alone, with no Rocq side.
"""
import glob
import os
import re
import sys

cache = sys.argv[1] == "--cache"
here = os.path.dirname(os.path.abspath(__file__))
root = os.path.normpath(os.path.join(here, ".."))

# function name -> the module path below Spec/ and Proof/ (`go_etcd_io.raft.v3.tracker.NewInflights`)
# (a bare `<fn>` shared by two packages, as `Error` of `rpctypes` and `status`, is
# ambiguous: such a function is named `<last component of pkg>_<fn>` only)
where, ambiguous = {}, set()
for dp, _, fs in os.walk(os.path.join(root, "Spec")):
    for f in fs:
        if f.endswith(".lean"):
            rel = os.path.relpath(os.path.join(dp, f), os.path.join(root, "Spec"))[:-len(".lean")]
            *pkg, stem = rel.split(os.sep)
            qual = pkg[-1] + "_" + stem
            assert qual not in where, f"two specs for {qual}"
            where[qual] = ".".join(pkg + [stem])
            if stem in where:
                ambiguous.add(stem)
            where[stem] = where[qual]
for name in ambiguous:
    del where[name]


def spec_file(fn):
    return os.path.join(root, "Spec", *where[fn].split(".")) + ".lean"

fns, callees, external = [], {}, set()
if not cache:
    rocq = sys.argv[1]
    fns = sorted(os.path.basename(f)[5:-2] for f in glob.glob(os.path.join(rocq, "spec_*.v")))
    modtype = {}
    for fn in fns:
        m = re.search(r"Module Type (\w+)\.", open(os.path.join(rocq, f"spec_{fn}.v")).read())
        modtype[m.group(1)] = fn
    for fn in fns:
        src = open(os.path.join(rocq, f"postulates_{fn}.v")).read()
        callees[fn] = [modtype[n] for n in re.findall(r"Include (\w+)\.", src)]

# Lean-first functions: no spec_/postulates_ files; `etc/link-lean-first.txt`
# (`etc/link-lean-first-cache.txt` for the cache)
with open(os.path.join(here, "link-lean-first-cache.txt" if cache else "link-lean-first.txt")) as f:
    for line in f:
        line = line.split("#")[0].strip()
        if not line:
            continue
        fn, _, cs = line.partition(":")
        fn = fn.strip()
        # a Rocq-side function may be listed to override its postulates (a Rocq
        # `Axiom` proved here from callees the Rocq does not have)
        if fn not in callees:
            fns.append(fn)
        if cs.strip() == "@":
            # linked in its own package's `Link.lean` (the btree): imported, not emitted
            external.add(fn)
            cs = ""
        callees[fn] = cs.split()
fns.sort()

spec = {}
for fn in fns:
    src = open(spec_file(fn)).read()
    m = re.search(r"^abbrev ([\w.«»]+)\.spec\b", src, re.M)
    # the namespaces below `EtcdGrove` the spec is declared in (`btree` for the btree's)
    nss = re.findall(r"^namespace (\S+)", src, re.M)
    inner = nss[nss.index("EtcdGrove") + 1:] if "EtcdGrove" in nss else []
    spec[fn] = ".".join(inner + [m.group(1)])

# The specs stated at `HeapGS HasLC.hasLC GF` (the ghost state holds an invariant).
haslc = {fn for fn in fns
         if "HeapGS HasLC.hasLC" in open(spec_file(fn)).read()}


def result(fn):
    """`a.b.M` ↦ `a.b.wp_M`, `F` ↦ `wp_F`."""
    parts = spec[fn].split(".")
    last = parts[-1].strip("«»")
    return ".".join(parts[:-1] + [f"wp_{last}"])


order, seen = [], set()


def visit(fn):
    if fn in seen:
        return
    seen.add(fn)
    for c in callees[fn]:
        visit(c)
    order.append(fn)


for fn in fns:
    visit(fn)

if cache:
    out = ["""/-
The `cache` package's proofs, every proof instantiated with its
callees' results. All of them are Lean-first, listed with their callees in
`etc/link-lean-first-cache.txt`. Generated by `etc/gen-link.py --cache` -- do not edit by
hand.

`#print axioms` on a result is its trust base.
-/""", "module", ""]
    out.extend(f"public import Proof.{where[fn]}" for fn in fns if fn not in external)
    out.extend(sorted({"public import Proof." + ".".join(where[fn].split(".")[:-1] + ["Link"])
                       for fn in external}))
    out.append("""
@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.cache.v3
""")
    out.append("""section links
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]
""")
    def emit_cache(fn):
        args = " ".join(result(c) for c in callees[fn])
        body = f"{spec[fn]}.wp_proof" + (f" {args}" if args else "")
        # the specs with ghost state (the store's) take `[AllG GF]`
        allg = " [AllG GF]" if "[AllG GF]" in open(spec_file(fn)).read() else ""
        return (f"theorem {result(fn)}{allg} :\n    {spec[fn]}.spec (GF := GF) (hG := hG) :=\n"
                f"  {body}\n")

    generic = [fn for fn in order if fn not in haslc and fn not in external]
    special = [fn for fn in order if fn in haslc and fn not in external]
    assert all(c not in haslc for fn in generic for c in callees[fn])
    out.extend(emit_cache(fn) for fn in generic)
    out.append("end links\n")
    if special:
        out.append("""/-! The specs stated at `HeapGS HasLC.hasLC GF`: those using channels, `sync.Once` or
`context` (Perennial states them there: their invariants need later credits). -/
section links_hasLC
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]
""")
        out.extend(emit_cache(fn) for fn in special)
        out.append("end links_hasLC\n")
    out.append("end EtcdGrove\nend Perennial")
    print("\n".join(out))
    sys.exit(0)

out = []
out.append("""/-
Port of `election_proof/election.v` and the `link_*.v` files (857d09190): every proof
instantiated with its callees' results, in the order of its `postulates_*.v`.
Generated by `etc/gen-link.py` -- do not edit by hand.

`#print axioms` on a result is its trust base: an `axiom` is the trust boundary (the
`Proof/<fn>.lean` of a function outside the scope), `sorryAx` is unfinished work.
-/""")
out.append("module")
out.append("")
for fn in fns:
    out.append(f"public import Proof.{where[fn]}")
out.append("""
@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3
""")

VARS = """variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
{heap}
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]
"""


def emit(fn):
    args = " ".join(result(c) for c in callees[fn])
    body = f"{spec[fn]}.wp_proof" + (f" {args}" if args else "")
    return (f"theorem {result(fn)} :\n    {spec[fn]}.spec (GF := GF) (hG := hG) :=\n"
            f"  {body}\n")


generic = [fn for fn in order if fn not in haslc]
special = [fn for fn in order if fn in haslc]
assert all(c not in haslc for fn in generic for c in callees[fn])
out.append("section links\n" + VARS.format(
    heap="variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]\nvariable [AllG GF]"))
out.extend(emit(fn) for fn in generic)
out.append("end links\n")
out.append("""/-! The specs stated at `HeapGS HasLC.hasLC GF`: the ghost state holds an
invariant (`raftCommitInv`), whose world is the heap's only at `.hasLC`. -/""")
out.append("section links_hasLC\n" + VARS.format(
    heap="variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]\nvariable [AllG GF]"))
out.extend(emit(fn) for fn in special)
out.append("end links_hasLC\n\nend EtcdGrove\nend Perennial")
print("\n".join(out))
