/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/raftNode__onStop.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.raftNode__onStop

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem raftNode.onStop.wp_proof :
    raftNode.onStop.spec (GF := GF) (hG := hG) := by
  intro E γ r
  wp_start as ⟨#Hr, Hdone⟩
  iunfold isRaftNode at Hr
  iNamed Hr
  iunfold isRaftNodeIfc at Hni
  icases Hni with ⟨%ni, %Hnieq, #HReady, #HAdv, #HTick, #HStop⟩
  subst Hnieq
  iunfold isRNTicker at Htki
  icases Htki with ⟨%c, #Hc, #Hcc, #HtkStop⟩
  iunfold isRNTransport at Htri
  icases Htri with ⟨%ti, %Htieq, #HSend, #HTrStop⟩
  subst Htieq
  iunfold isRNWal at Hsti
  icases Hsti with ⟨%si, %Hsieq, #HSave, #HClose⟩
  subst Hsieq
  iunfold rnDoneTok at Hdone
  icases Hdone with ⟨%dnc', #Hdnc', Hbc⟩
  icombine Hdnc Hdnc' gives %Heq
  subst Heq
  ihave #Hzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  wp_auto
  rw [method_unfold (t := go.GoType.PointerType raftNode.ty) (m := go!"Stop")]
  wp_auto
  rw [method_unfold (t := go.GoType.PointerType raftNodeConfig.ty) (m := go!"Stop")]
  wp_auto
  wp_apply HStop
  wp_apply HtkStop
  wp_apply HTrStop
  wp_apply HClose
  wp_apply wp_broadcast_chan_close dnc γ.done iprop(True) $$ [$Hbc]
  · imodintro; itrivial
  iintro -
  wp_auto
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
