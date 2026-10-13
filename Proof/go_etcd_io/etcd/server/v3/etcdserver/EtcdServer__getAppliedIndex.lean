/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__getAppliedIndex.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__getAppliedIndex

@[expose] public section

set_option linter.unusedSectionVars false

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

theorem EtcdServer.getAppliedIndex.wp_proof : EtcdServer.getAppliedIndex.spec (GF := GF) (hG := hG) := by
  intro s E γr
  wp_start as #Hl
  ihave #Hatomic : isPkgInit (PROP := IProp GF) pkg_id.sync.atomic $$ []
  · iPkgInit
  iunfold srvAppliedInv at Hl
  wp_auto
  wp_apply_core sync.atomic.Uint64.wp_Load (structFieldRef EtcdServer go!"appliedIndex" s)
    (DFrac.own 1) $$ [] [HΦ]
  · iexact Hatomic
  iinv Hl with Hi Hclose
  iapply fupd_mask_intro (Std.LawfulSet.empty_subset)
  iintro Hmask
  inext
  icases Hi with ⟨%v0, %L0, %M, Hv, Hauth, HM, %HMk, #HL0, #Hc0⟩
  iexists v0
  iframe Hv
  iintro Hv
  imod Hmask with -
  ihave #Hlb := monoNatLbOwn_get γr.applied _ _ $$ Hauth
  imod Hclose $$ [Hv Hauth HM] with -
  · inext; iexists v0, L0, M; iframe Hv Hauth HM HL0 Hc0; ipureintro; exact HMk
  imodintro
  wp_auto
  iapply HΦ
  iunfold appliedAtLeast
  iexact Hlb

end proof

end EtcdGrove
end Perennial
