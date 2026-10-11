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
       etc/gen-link.py --server > Proof/go_etcd_io/etcd/server/v3/etcdserver/Link.lean
       etc/gen-link.py --concurrency > Proof/go_etcd_io/etcd/client/v3/concurrency/Link.lean
       etc/gen-link.py --leasing > Proof/go_etcd_io/etcd/client/v3/leasing/Link.lean
       etc/gen-link.py --recipes > Proof/go_etcd_io/etcd/client/v3/experimental/recipes/Link.lean
       etc/gen-link.py --register > Proof/github_com/mit_pdos/etcd_grove/examples/register/Link.lean
       etc/gen-link.py --mvcc > Proof/go_etcd_io/etcd/server/v3/storage/mvcc/Link.lean
       etc/gen-link.py --adt > Proof/go_etcd_io/etcd/pkg/v3/adt/Link.lean

`--cache` links the proofs of etcd's `cache` package (`Proof/go_etcd_io/etcd/cache/v3/` and
the specs and proofs of its functions), which are all
Lean-first: they are read from etc/link-lean-first-cache.txt alone, with no Rocq side.
`--server` likewise links the proofs of etcd's server (the consistent index and the apply
thread, `Proof/go_etcd_io/etcd/server/v3/etcdserver/`), from etc/link-lean-first-server.txt;
its specs are also looked up in `EtcdDeps/Spec/` (etcd's own raft dependency, raft v3.7, whose
Go path is the fork's).
`--concurrency` links the proofs of `client/v3/concurrency` (`Session`) and of the clientv3
functions they and the next recipes use, from etc/link-lean-first-concurrency.txt, under the
concurrency package's assumptions. Its results are in the namespace `concurrency`, a clientv3
function's with the prefix `v3.` (`concurrency.v3.wp_OpPut`), and the specs are referred to by
their full names below `EtcdGrove`: the cache's Link links some of the same clientv3 functions
(under the cache's assumptions), and concurrency's `WithLease` shares its name with clientv3's.
`--leasing` links the proofs of `client/v3/leasing` (the lease cache) and of the clientv3,
etcdserverpb and standard-library functions they call, from etc/link-lean-first-leasing.txt,
under the leasing package's assumptions; as `--concurrency`, its results are in a namespace of
their own (`leasing`), a clientv3 function's with the prefix `v3.`.
`--recipes` links the proofs of `client/v3/experimental/recipes` (barrier, double barrier, queue,
priority queue, RWMutex) and of the clientv3 and concurrency functions they call, from
etc/link-lean-first-recipes.txt, under the recipes package's assumptions; as `--leasing`, its
results are in a namespace of their own (`recipes`), a clientv3 function's with the prefix `v3.`
and concurrency's with the prefix `concurrency.` (its specs' own namespace,
`recipes.concurrency.Session.wp_Client`).
A callee list `?` (`fn: ?`) marks a function specified but not proved yet (a later unit's): its
spec is a hypothesis (`h_<fn>`, `section links_pending`) of every result that reaches it.
`--mvcc` links the proofs of the KV core of etcd's `server/v3/storage/mvcc`
(`Proof/go_etcd_io/etcd/server/v3/storage/mvcc/`), from etc/link-lean-first-mvcc.txt.
`--adt` links the proofs of etcd's interval tree (`pkg/v3/adt`, `Proof/go_etcd_io/etcd/pkg/v3/adt/`),
from etc/link-lean-first-adt.txt: the tree's contract pending (`?`), the comparisons proved.
`--skip-unproved` (after the mode) leaves out the listed functions with no proof file yet (no
spec, or no `Proof/` file: a later unit's) and every function that reaches one, and names them
in the header: a package proved in units links what is done, from the full list.
`--register` links the register example's proofs (`examples/register`), from
etc/link-lean-first-register.txt; raft's functions it calls are `@` callees, linked in raft's
`Link.lean`, and its specs' `[RegStor GF]` (the storage registry) is passed on.
"""
import glob
import os
import re
import sys
import textwrap

# The Lean-first links: (callee list, what the links open, the package assumptions they
# are stated under, a description for the header, the module roots holding their specs).
LEAN_FIRST = {
    "--cache": ("link-lean-first-cache.txt", "go_etcd_io.etcd.cache.v3",
                "go_etcd_io.etcd.cache.v3.Assumptions", "The `cache` package's proofs", [""]),
    # etcdserver's assumptions include those of every package it imports (instances):
    # cindex's, schema's, raft v3.7's raftpb's, zap's, ..., which the other specs use
    "--server": ("link-lean-first-server.txt",
                 "go_etcd_io.etcd.server.v3.etcdserver.cindex go_etcd_io.etcd.server.v3.storage "
                 "go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.server.v3 "
                 "go_etcd_io.etcd.pkg.v3 go_uber_org go_etcd_io.raft.v3",
                 "go_etcd_io.etcd.server.v3.etcdserver.Assumptions",
                 "The etcd server's proofs (the consistent index and the apply thread)",
                 ["", "EtcdDeps"]),
    "--concurrency": ("link-lean-first-concurrency.txt",
                      "go_etcd_io.etcd.client.v3.concurrency go_etcd_io.etcd.api.v3",
                      "go_etcd_io.etcd.client.v3.concurrency.Assumptions",
                      "The `client/v3/concurrency` package's proofs (`Session`) and the clientv3 "
                      "functions they and the next recipes use", [""]),
    "--leasing": ("link-lean-first-leasing.txt",
                  "go_etcd_io.etcd.client.v3.leasing go_etcd_io.etcd.api.v3",
                  "go_etcd_io.etcd.client.v3.leasing.Assumptions",
                  "The `client/v3/leasing` package's proofs (the lease cache) and the functions "
                  "they call", [""]),
    # the mvcc KV core (etcd's server/v3/storage/mvcc)
    "--mvcc": ("link-lean-first-mvcc.txt", "go_etcd_io.etcd.server.v3.storage.mvcc",
               "go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions",
               "The mvcc KV core's proofs (etcd's `server/v3/storage/mvcc`)", [""]),
    # the interval tree (etcd's pkg/v3/adt), the watchable store's
    "--adt": ("link-lean-first-adt.txt", "go_etcd_io.etcd.pkg.v3.adt",
              "go_etcd_io.etcd.pkg.v3.adt.Assumptions",
              "The interval tree's proofs (etcd's `pkg/v3/adt`)", [""]),
    "--recipes": ("link-lean-first-recipes.txt",
                  "go_etcd_io.etcd.client.v3.experimental.recipes go_etcd_io.etcd.api.v3",
                  "go_etcd_io.etcd.client.v3.experimental.recipes.Assumptions",
                  "The `client/v3/experimental/recipes` package's proofs and the functions they "
                  "call", [""]),
    # the register example (examples/register): its proofs, over raft's (linked in raft's
    # `Link.lean`, the `@` callees) and the storage model `RegStor` gives
    "--register": ("link-lean-first-register.txt",
                   "github_com.mit_pdos.etcd_grove.examples.register go_etcd_io.raft.v3",
                   "github_com.mit_pdos.etcd_grove.examples.register.Assumptions",
                   "The register example's proofs (`examples/register`)", [""]),
}
# The mode whose results are put in a namespace of their own (see the docstring).
NAMESPACED = {"--concurrency": "concurrency", "--leasing": "leasing", "--recipes": "recipes"}
mode = LEAN_FIRST.get(sys.argv[1])
cache = mode is not None
here = os.path.dirname(os.path.abspath(__file__))
root = os.path.normpath(os.path.join(here, ".."))

# function name -> the module path below Spec/ and Proof/ (`go_etcd_io.raft.v3.tracker.NewInflights`)
# (a bare `<fn>` shared by two packages, as `Error` of `rpctypes` and `status`, is
# ambiguous: such a function is named `<last component of pkg>_<fn>` only)
# (`prefix`: the module root of a spec outside `Spec/`, as `EtcdDeps.`)
where, prefix, ambiguous = {}, {}, set()
for mroot in (mode[4] if cache else [""]):
    spec_dir = os.path.join(root, mroot, "Spec")
    for dp, _, fs in os.walk(spec_dir):
        for f in fs:
            if f.endswith(".lean"):
                rel = os.path.relpath(os.path.join(dp, f), spec_dir)[:-len(".lean")]
                *pkg, stem = rel.split(os.sep)
                qual = pkg[-1] + "_" + stem
                assert qual not in where, f"two specs for {qual}"
                where[qual] = ".".join(pkg + [stem])
                prefix[qual] = mroot + "." if mroot else ""
                if stem in where:
                    ambiguous.add(stem)
                where[stem], prefix[stem] = where[qual], prefix[qual]
for name in ambiguous:
    del where[name]


def spec_file(fn):
    return os.path.join(root, prefix[fn].rstrip("."), "Spec", *where[fn].split(".")) + ".lean"


def proof_module(fn):
    return f"{prefix[fn]}Proof.{where[fn]}"

fns, callees, external, pending = [], {}, set(), set()
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
with open(os.path.join(here, mode[0] if cache else "link-lean-first.txt")) as f:
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
        if cs.strip() == "?":
            # specified, not proved yet (a later unit's): a hypothesis of the results that
            # reach it (`section links_pending`)
            pending.add(fn)
            cs = ""
        callees[fn] = cs.split()
fns.sort()

# `--skip-unproved`: leave out the functions with no proof file yet, and those reaching one
skipped = set()
if cache and "--skip-unproved" in sys.argv[2:]:
    def proved(fn):
        return fn in where and os.path.exists(
            os.path.join(root, prefix[fn].rstrip("."), "Proof", *where[fn].split(".")) + ".lean")
    skipped = {fn for fn in fns if not proved(fn)}
    changed = True
    while changed:
        changed = False
        for fn in fns:
            if fn not in skipped and any(c in skipped for c in callees[fn]):
                skipped.add(fn)
                changed = True
    fns = [fn for fn in fns if fn not in skipped]

spec = {}
for fn in fns:
    src = open(spec_file(fn)).read()
    m = re.search(r"^abbrev ([\w.«»']+)\.spec\b", src, re.M)
    # the namespaces below `EtcdGrove` the spec is declared in (`btree` for the btree's)
    nss = re.findall(r"^namespace (\S+)", src, re.M)
    inner = nss[nss.index("EtcdGrove") + 1:] if "EtcdGrove" in nss else []
    spec[fn] = ".".join(inner + [m.group(1)])

# The specs stated at `HeapGS HasLC.hasLC GF` (the ghost state holds an invariant).
haslc = {fn for fn in fns
         if "HeapGS HasLC.hasLC" in open(spec_file(fn)).read()}


nsd = NAMESPACED.get(sys.argv[1])


def result(fn):
    """`a.b.M` ↦ `a.b.wp_M`, `F` ↦ `wp_F` (in a namespaced mode: relative to its namespace, a
    clientv3 function's with the prefix `v3.`)."""
    parts = spec[fn].split(".")
    last = parts[-1].strip("«»")
    if nsd:
        if parts[0] == nsd:
            parts = parts[1:]
        elif where[fn].split(".")[:-1] == ["go_etcd_io", "etcd", "client", "v3"]:
            parts = ["v3"] + parts
    return ".".join(parts[:-1] + [f"wp_{last}"])


def specref(fn):
    """The spec's name as the Link refers to it: in a namespaced mode, below `EtcdGrove`."""
    return f"EtcdGrove.{spec[fn]}" if nsd else spec[fn]


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
    listfile, opens, assumptions, what, _ = mode
    out = [f"""/-
{what}, every proof instantiated with its
callees' results. All of them are Lean-first, listed with their callees in
`etc/{listfile}`. Generated by `etc/gen-link.py {sys.argv[1]}` -- do not edit by
hand.

`#print axioms` on a result is its trust base.""" + ("\n\n" + textwrap.fill(
        "Generated with `--skip-unproved`: not linked yet (no proof file, or reaching such a "
        "function): " + ", ".join(f"`{fn}`" for fn in sorted(skipped)) + ".", 96,
        break_on_hyphens=False) if skipped else "") + """
-/""", "module", ""]
    out.extend(f"public import {proof_module(fn)}" for fn in fns
               if fn not in external and fn not in pending)
    out.extend(f"public import {prefix[fn]}Spec.{where[fn]}" for fn in fns if fn in pending)
    out.extend(sorted({"public import Proof." + ".".join(where[fn].split(".")[:-1] + ["Link"])
                       for fn in external}))
    out.append(f"""
@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
""" + (f"namespace {nsd}\n" if nsd else "") + f"""
open Iris Iris.BI {opens}
""")
    out.append(f"""section links
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {{hlc : HasLC}} {{GF : BundledGFunctors}} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : {assumptions}]
""")
    def hyp(fn):
        return "h_" + fn

    def arg(fn, c):
        if c in pending:
            return hyp(c)
        if c in blocked:
            # a result of `links_pending`: applied to the pending hypotheses (section variables
            # are not applied automatically)
            return "(" + result(c) + " " + " ".join(hyp(p) for p in sorted(pending)) + ")"
        # a callee's result named like the theorem's last component (`leaseCache.wp_evalCmp`
        # calling `wp_evalCmp`) would resolve to the theorem itself: qualify it
        r = result(c)
        if nsd and "." in result(fn) and r == result(fn).split(".")[-1]:
            return f"EtcdGrove.{nsd}.{r}"
        return r

    def emit_cache(fn):
        args = " ".join(arg(fn, c) for c in callees[fn])
        body = f"{specref(fn)}.wp_proof" + (f" {args}" if args else "")
        # the specs with ghost state (the store's) take `[AllG GF]`
        src = open(spec_file(fn)).read()
        allg = " [AllG GF]" if "[AllG GF]" in src and fn not in blocked else ""
        # the register's specs take its storage registry
        allg += " [RegStor GF]" if "[RegStor GF]" in src else ""
        # mvcc's index specs use the btree through the cache's interface (its assumptions), and
        # so does every result that links one of them
        allg += " [go_etcd_io.etcd.cache.v3.Assumptions]" if fn in cache_assumptions else ""
        # ... or, stated over any raft storage model, that (the register's transport)
        if "[RegStor GF]" not in src and "[StorageModel GF]" in src:
            allg += " [StorageModel GF]"
        return (f"theorem {result(fn)}{allg} :\n    {specref(fn)}.spec (GF := GF) (hG := hG) :=\n"
                f"  {body}\n")

    cache_assumptions = set()
    for fn in order:
        if fn in external:
            continue
        if ("variable [go_etcd_io.etcd.cache.v3.Assumptions]" in open(spec_file(fn)).read()
                or any(c in cache_assumptions for c in callees[fn])):
            cache_assumptions.add(fn)

    # the results that reach a pending function, and the pending functions themselves: emitted
    # last, with the pending specs as hypotheses
    blocked = set(pending)
    for fn in order:
        if any(c in blocked for c in callees[fn]):
            blocked.add(fn)
    generic = [fn for fn in order if fn not in haslc and fn not in external and fn not in blocked]
    special = [fn for fn in order if fn in haslc and fn not in external and fn not in blocked]
    assert all(c not in haslc for fn in generic for c in callees[fn])
    out.extend(emit_cache(fn) for fn in generic)
    out.append("end links\n")
    if special:
        out.append(f"""/-! The specs stated at `HeapGS HasLC.hasLC GF`: those using channels, `sync.Once` or
`context` (Perennial states them there: their invariants need later credits). -/
section links_hasLC
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {{GF : BundledGFunctors}} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : {assumptions}]
""")
        out.extend(emit_cache(fn) for fn in special)
        out.append("end links_hasLC\n")
    later = [fn for fn in order if fn in blocked and fn not in pending]
    if later:
        hyps = "\n".join(f"variable ({hyp(fn)} : {specref(fn)}.spec (GF := GF) (hG := hG))"
                         for fn in sorted(pending))
        names = " ".join(hyp(fn) for fn in sorted(pending))
        out.append(f"""/-! The results that reach a function specified but not proved yet (a later unit's):
its spec is a hypothesis (`h_<fn>`) of each of them. -/
section links_pending
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {{GF : BundledGFunctors}} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : {assumptions}]
{hyps}
include {names}
""")
        out.extend(emit_cache(fn) for fn in later)
        out.append("end links_pending\n")
    out.append((f"end {nsd}\n" if nsd else "") + "end EtcdGrove\nend Perennial")
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
    out.append(f"public import {proof_module(fn)}")
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
    heap="variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]"))
out.extend(emit(fn) for fn in generic)
out.append("end links\n")
out.append("""/-! The specs stated at `HeapGS HasLC.hasLC GF`: the ghost state holds an
invariant (`raftCommitInv`), whose world is the heap's only at `.hasLC`. -/""")
out.append("section links_hasLC\n" + VARS.format(
    heap="variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]"))
out.extend(emit(fn) for fn in special)
out.append("end links_hasLC\n\nend EtcdGrove\nend Perennial")
print("\n".join(out))
