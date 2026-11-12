/-
Package initialization for the Lock service's server `server/v3/etcdserver/api/v3lock` and its
messages `v3lockpb` (the auth plan's A3c, 2026-10-24; `notes/decisions.md`, "A3c of the auth plan:
Lock and Election"): no facts (`True`). Proved from `initialize'` (`Init.lean`). Lean-first (no
Rocq counterpart).
-/
module

public import Code.go_etcd_io.etcd.server.v3.etcdserver.api.v3lock
public import GeneratedProof.go_etcd_io.etcd.server.v3.etcdserver.api.v3lock
public import Proof.go_etcd_io.etcd.client.v3.concurrency.InvMutex

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance v3lockpb_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3lock.v3lockpb :=
  define_is_pkg_init iprop(True)
instance v3lockpb_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3lock.v3lockpb :=
  build_get_is_pkg_init_wf

instance v3lock_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3lock :=
  define_is_pkg_init iprop(True)
instance v3lock_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3lock :=
  build_get_is_pkg_init_wf

end init

end Perennial
