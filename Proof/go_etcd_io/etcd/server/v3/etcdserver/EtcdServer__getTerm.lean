/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__getTerm.lean`. Lean-first (no Rocq
counterpart); the request path's unit 3b (2026-10-12).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__getTerm

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem EtcdServer.getTerm.wp_proof : EtcdServer.getTerm.spec (GF := GF) (hG := hG) := by
  intro s
  wp_start as #Hl
  ihave #Hatomic : isPkgInit (PROP := IProp GF) pkg_id.sync.atomic $$ []
  · iPkgInit
  wp_auto
  wp_apply_core sync.atomic.Uint64.wp_Load (srvTermAddr s) (DFrac.own 1) $$ [] [HΦ]
  · iexact Hatomic
  iinv Hl with Hi Hclose
  iapply fupd_mask_intro (Std.LawfulSet.empty_subset)
  iintro Hmask
  inext
  icases Hi with ⟨%v0, Hv⟩
  iexists v0
  iframe Hv
  iintro Hv
  imod Hmask with -
  imod Hclose $$ [Hv] with -
  · inext; iexists v0; iexact Hv
  imodintro
  wp_auto
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
