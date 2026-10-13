/- Lean-first (no Rocq counterpart). -/
module

public import Spec.go_etcd_io.raft.v3.node__ReadIndex
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

/-- The one-entry batch `[]pb.Entry{{Data: rctx}}`, read-only, then `step` of the request:
a message from the network (`netP`) as far as `run` is concerned. -/
theorem node.ReadIndex.wp_proof
    (wp_node_step : node.step.spec (GF := GF) (hG := hG)) :
    node.ReadIndex.spec (GF := GF) (hG := hG) := by
  intro γ id n rctx c Lc Hsing
  wp_start as ⟨#Hnode, #Hpd, #Hrq, Hcred⟩
  wp_auto
  wp_apply wp_slice_literal (l := [({ (zero_val raftpb.Entry) with Data' := rctx } :
    raftpb.Entry)])
  isplitr
  · ipureintro; rfl
  iintro %esl ⟨Hes, Hcap⟩
  imod ownSlice_persist _ _ _ $$ Hes with #Hes
  imod termLB_zero (GF := GF) γ.bud with #Hlb
  wp_auto
  have hR : (W32 15 : w32) = MsgReadIndex := rfl
  wp_apply wp_node_step γ id n _ $$ [Hcap Hcred]
  · iframe Hnode
    unfold stepP
    ileft
    unfold netP
    isplitr
    · ipureintro
      refine ⟨by simp [netStepTypes, MsgReadIndex], fun h => absurd hR h, fun _ => rfl,
        fun h => ?_, fun h => ?_⟩
      · exfalso
        rcases h with h | h | h | h <;>
          simp [MsgApp, MsgHeartbeat, MsgHeartbeatResp, MsgReadIndexResp] at h
      · exfalso; simp [MsgAppResp] at h
    iexists [({ (zero_val raftpb.Entry) with Data' := rctx } : raftpb.Entry)], []
    iframe Hes Hcap
    isplitr
    · iapply ownSlice_nil
    isplitr
    · ipureintro
      refine ⟨fun Hc => ?_, fun _ => Hsing⟩
      unfold campaignTransfer at Hc; simp at Hc
    isplitr
    · imodintro
      iintro %ty %Hty
      rw [show mtypeOf (W32 15) = some .readIndex from rfl] at Hty
      cases Hty
      unfold isMessage absMsg absMsgFrom
      iexists ({ (zero_val raftpb.Entry) with Data' := rctx } : raftpb.Entry), c, Lc
      isplitr
      · ipureintro; rfl
      iframe Hpd Hrq
    isplitr
    · iExactEq Hlb; rfl
    rw [if_pos hR]
    iexact Hcred
  iintro %err -
  wp_auto
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
