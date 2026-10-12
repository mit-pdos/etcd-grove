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
       etc/gen-link.py --register > Proof/github_com/mit_pdos/etcd_grove/examples/register/Link.lean
       etc/gen-link.py --bbolt > Proof/go_etcd_io/bbolt/internal/common/Link.lean
       etc/gen-link.py --bbolt-root > Proof/go_etcd_io/bbolt/Link.lean
       etc/gen-link.py --bbolt-freelist > Proof/go_etcd_io/bbolt/internal/freelist/Link.lean

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
`--bbolt` links bbolt's proofs (`internal/common` so far), from etc/link-lean-first-bbolt.txt,
in the namespace `bbolt` (their specs' namespace). `--bbolt-root` links those of bbolt's root
package (and the axioms of the file and memory-map model, `Proof/os/FileModel.lean`, which
they call), from etc/link-lean-first-bbolt-root.txt.
`--register` links the register example's proofs (`examples/register`), from
etc/link-lean-first-register.txt; raft's functions it calls are `@` callees, linked in raft's
`Link.lean`, and its specs' `[RegStor GF]` (the storage registry) is passed on.
"""
import glob
import os
import re
import sys

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
    # the register example (examples/register): its proofs, over raft's (linked in raft's
    # `Link.lean`, the `@` callees) and the storage model `RegStor` gives
    "--register": ("link-lean-first-register.txt",
                   "github_com.mit_pdos.etcd_grove.examples.register go_etcd_io.raft.v3",
                   "github_com.mit_pdos.etcd_grove.examples.register.Assumptions",
                   "The register example's proofs (`examples/register`)", [""]),
    # bbolt (go.etcd.io/bbolt): its proofs, in namespace `bbolt`
    "--bbolt": ("link-lean-first-bbolt.txt", "go_etcd_io.bbolt.internal.common",
                "go_etcd_io.bbolt.internal.common.Assumptions", "bbolt's proofs", [""]),
    "--bbolt-root": ("link-lean-first-bbolt-root.txt", "go_etcd_io.bbolt",
                     "go_etcd_io.bbolt.Assumptions",
                     "bbolt's root package's proofs and the file model's axioms", [""]),
    "--bbolt-freelist": ("link-lean-first-bbolt-freelist.txt", "go_etcd_io.bbolt.internal.freelist",
                         "go_etcd_io.bbolt.internal.freelist.Assumptions",
                         "bbolt's internal/freelist proofs", [""]),
}
# bbolt reaches `hash` only through `hash/fnv`, so its `Assumptions` lack `hash`'s, which the
# meta checksum's specs (`Meta.Sum64`, ...) take: a Goose gap, an instance hypothesis until fixed
BBOLT_HASH = """-- `hash.Hash64`'s type: bbolt's `Assumptions` do not include `hash`'s (it reaches `hash` only
-- through `hash/fnv`)
variable [hash_sem : _root_.Perennial.hash.Hash64.TypeAssumptions]
-- the ghost state of the database's predicates (`DBPred.lean`)
variable [AllG GF]
"""
# the root package's proofs also take `os.FileInfo`'s assumptions (an alias Perennial's `os`
# keeps opaque, `Proof/os/FileInfoAlias.lean`)
BBOLT_ROOT = """variable [os_fi : OsFileInfoAssumptions (GF := GF)]
-- the platform (`Proof/runtime/GOOS.lean`)
variable [linux : GOOSLinux]
"""
# The mode whose results are put in a namespace of their own (see the docstring).
NAMESPACED = {"--concurrency": "concurrency", "--bbolt": "bbolt", "--bbolt-root": "bbolt",
              "--bbolt-freelist": "bbolt"}
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
        callees[fn] = cs.split()
fns.sort()

spec = {}
# a second spec of a function (`<T>.<M>.wspec`, proved by `<T>.<M>.wp_wproof`: the writer's
# view of a function a reader also calls) is linked as `<T>.wp_<M>_w`
wspec = set()
for fn in fns:
    src = open(spec_file(fn)).read()
    m = re.search(r"^abbrev ([\w.«»']+)\.spec\b", src, re.M)
    if m is None:
        m = re.search(r"^abbrev ([\w.«»']+)\.wspec\b", src, re.M)
        wspec.add(fn)
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
    suffix = "_w" if fn in wspec else ""
    return ".".join(parts[:-1] + [f"wp_{last}{suffix}"])


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

`#print axioms` on a result is its trust base.
-/""", "module", ""]
    out.extend(f"public import {proof_module(fn)}" for fn in fns if fn not in external)
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
""" + (BBOLT_HASH if sys.argv[1] in ("--bbolt", "--bbolt-root", "--bbolt-freelist") else "")
      + (BBOLT_ROOT if sys.argv[1] == "--bbolt-root" else ""))
    def emit_cache(fn):
        # qualified in a namespaced mode: in `theorem DB.wp_munmap`, a bare `wp_munmap` would be
        # `DB.wp_munmap` itself
        args = " ".join((f"EtcdGrove.{nsd}.{result(c)}" if nsd else result(c))
                        for c in callees[fn])
        sp, pf = ("wspec", "wp_wproof") if fn in wspec else ("spec", "wp_proof")
        body = f"{specref(fn)}.{pf}" + (f" {args}" if args else "")
        # the specs with ghost state (the store's) take `[AllG GF]`
        src = open(spec_file(fn)).read()
        allg = " [AllG GF]" if "[AllG GF]" in src else ""
        # the register's specs take its storage registry
        allg += " [RegStor GF]" if "[RegStor GF]" in src else ""
        return (f"theorem {result(fn)}{allg} :\n    {specref(fn)}.{sp} (GF := GF) (hG := hG) :=\n"
                f"  {body}\n")

    generic = [fn for fn in order if fn not in haslc and fn not in external]
    special = [fn for fn in order if fn in haslc and fn not in external]
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
