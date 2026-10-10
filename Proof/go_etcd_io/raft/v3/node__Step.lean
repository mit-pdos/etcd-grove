/- Lean-first (no Rocq counterpart). -/
module

public import Spec.go_etcd_io.raft.v3.node__Step
public import Spec.go_etcd_io.raft.v3.node__step
public import Spec.go_etcd_io.raft.v3.IsLocalMsg
public import Spec.go_etcd_io.raft.v3.IsLocalMsgTarget

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
variable [AllG GF]

/-- A local message from a remote sender is dropped; anything else goes to `step`. -/
theorem node.Step.wp_proof
    (wp_IsLocalMsg : IsLocalMsg.spec (GF := GF) (hG := hG))
    (wp_IsLocalMsgTarget : IsLocalMsgTarget.spec (GF := GF) (hG := hG))
    (wp_node_step : node.step.spec (GF := GF) (hG := hG)) :
    node.Step.spec (GF := GF) (hG := hG) := by
  intro γ id n m
  wp_start as ⟨#Hnode, Hnet⟩
  iunfold netP at Hnet
  icases Hnet with ⟨%Hok, Hnet⟩
  have Hty : 0 ≤ sint.Z m.Type' := by
    have h := Hok.1
    simp only [netStepTypes, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h <;> rw [h] <;> decide
  wp_auto
  wp_apply wp_IsLocalMsg m.Type' Hty as %b -
  cases b
  · wp_auto
    wp_apply wp_node_step γ id n m $$ [Hnet]
    · iframe Hnode
      unfold netP
      iframe Hnet
      ipureintro; exact Hok
    iintro %err -
    wp_auto
    iapply HΦ
    itrivial
  · wp_auto
    wp_apply wp_IsLocalMsgTarget m.From'
    wp_if_destruct
    · wp_apply wp_node_step γ id n m $$ [Hnet]
      · iframe Hnode
        unfold netP
        iframe Hnet
        ipureintro; exact Hok
      iintro %err -
      wp_auto
      iapply HΦ
      itrivial
    · iapply HΦ
      itrivial

end proof

end EtcdGrove
end Perennial
