/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/raftNode__ReadIndex.lean`. Lean-first (no Rocq counterpart); the request path's unit 4b.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.raftNode__ReadIndex

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

theorem raftNode.ReadIndex.wp_proof : raftNode.ReadIndex.spec (GF := GF) (hG := hG) := by
  intro E γ r ctx cd sl id n Qr
  wp_start as ⟨#Hr, #Hctx, #Hsl, #Hc, #HRA, Hcred, Hfresh⟩
  iunfold isRaftNode at Hr
  iNamed Hr
  iunfold isRaftNodeIfc at Hni
  icases Hni with ⟨%ni, %Hnieq, -, -, -, -, -, #HRI⟩
  subst Hnieq
  ihave Hcred' := rnReadCred_of_srv E γ $$ [Hcred]
  · iframe Henv Hcred
  rw [method_unfold (t := go.GoType.PointerType raftNodeConfig.ty) (m := go!"ReadIndex")]
  wp_pures
  (try wp_auto)
  wp_apply HRI $$ %ctx %cd %sl %id %n %Qr [Hcred' Hfresh] as %err Hpost
  · iframe Hctx Hc Hsl HRA Hcred' Hfresh
  iapply HΦ
  iexact Hpost

end proof

end EtcdGrove
end Perennial
