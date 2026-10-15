/- Lean-first (no Rocq counterpart), 2026-10-13. -/
module

public import Spec.go_etcd_io.raft.v3.node__ForgetLeader
public import Spec.go_etcd_io.raft.v3.node__step

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `step` of the literal message, a local one (`netP_local`). -/
theorem node.ForgetLeader.wp_proof
    (wp_node_step : node.step.spec (GF := GF) (hG := hG)) :
    node.ForgetLeader.spec (GF := GF) (hG := hG) := by
  intro γ id n
  wp_start as #Hnode
  wp_auto
  imod termLB_zero (GF := GF) γ.bud with #Hlb
  imod rdCred_zero_upd (GF := GF) γ.raft with Hcr
  imod tickCred_zero (GF := GF) γ.bud with Htc
  wp_apply wp_node_step γ id n _ $$ [Hcr Htc]
  · iframe Hnode
    unfold stepP
    ileft
    iapply netP_local γ id _ (by first | exact .inl rfl | exact .inr (.inl rfl) | exact .inr (.inr (.inl rfl)) | exact .inr (.inr (.inr rfl))) (by rfl) (by rfl) (by rfl) $$ Hlb Hcr Htc
  iintro %err -
  wp_auto
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
