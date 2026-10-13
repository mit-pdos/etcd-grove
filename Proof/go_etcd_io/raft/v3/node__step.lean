/- Lean-first (no Rocq counterpart). -/
module

public import Spec.go_etcd_io.raft.v3.node__step
public import Spec.go_etcd_io.raft.v3.node__stepWithWaitOption

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

/-- `stepWithWaitOption(ctx, m, false)`: `m` is not a proposal (`NetMsgOk`). -/
theorem node.step.wp_proof
    (wp_node_stepWithWaitOption : node.stepWithWaitOption.spec (GF := GF) (hG := hG)) :
    node.step.spec (GF := GF) (hG := hG) := by
  intro γ id n m
  wp_start as ⟨#Hnode, Hstep⟩
  unfold stepP
  icases Hstep with (Hnet | Hfwd)
  rotate_left
  · -- a forwarded proposal (2026-10-10)
    wp_auto
    wp_apply wp_node_stepWithWaitOption γ id n m false $$ [Hfwd]
    · iframe Hnode
      unfold stepArg
      iright; iright
      iframe Hfwd
      ipureintro; rfl
    iintro %err -
    wp_auto
    iapply HΦ
    itrivial
  iunfold netP at Hnet
  icases Hnet with ⟨%Hok, Hnet⟩
  wp_auto
  wp_apply wp_node_stepWithWaitOption γ id n m false $$ [Hnet]
  · iframe Hnode
    unfold stepArg
    ileft
    isplitr
    · ipureintro
      have h := Hok.1
      simp only [netStepTypes, List.mem_cons, List.not_mem_nil, or_false] at h
      intro he
      rw [he] at h
      rcases h with h | h | h | h | h | h | h | h <;> simp [MsgProp, MsgApp, MsgAppResp, MsgVote,
        MsgVoteResp, MsgHeartbeat, MsgHeartbeatResp, MsgReadIndex, MsgReadIndexResp] at h
    unfold netP
    iframe Hnet
    ipureintro; exact Hok
  iintro %err -
  wp_auto
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
