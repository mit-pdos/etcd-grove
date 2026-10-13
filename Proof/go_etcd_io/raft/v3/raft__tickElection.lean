/- Lean-first (no Rocq counterpart). -/
module

public import Spec.go_etcd_io.raft.v3.raft__tickElection
public import Spec.go_etcd_io.raft.v3.raft__promotable
public import Spec.go_etcd_io.raft.v3.raft__pastElectionTimeout

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

/-- A premise of `Step` about another message type: `MsgHup` (`W32 0`) is not it. -/
local macro "msg_ne" : tactic => `(tactic| (intro Hc; simp [MsgHup, MsgVote, MsgVoteResp,
  MsgPreVote, MsgPreVoteResp, MsgApp, MsgHeartbeat, MsgAppResp, MsgHeartbeatResp, MsgSnap,
  MsgBeat, MsgProp, MsgStorageAppendResp, MsgStorageApplyResp, MsgReadIndex,
  MsgReadIndexResp, MsgForgetLeader, MsgUnreachable, MsgSnapStatus, MsgTimeoutNow, MsgTransferLeader] at Hc))

/-- `electionElapsed++`, then possibly the campaign: `raft.Step` of a `MsgHup`. -/
theorem raft.tickElection.wp_proof
    (wp_promotable : raft.promotable.spec (GF := GF) (hG := hG))
    (wp_pastElectionTimeout : raft.pastElectionTimeout.spec (GF := GF) (hG := hG))
    (wp_raft_Step : raft.Step.spec (GF := GF) (hG := hG)) :
    raft.tickElection.spec (GF := GF) (hG := hG) := by
  intro cfg γ r id s ps Hcfg Hterm Hrel
  wp_start as H
  iNamed H
  wp_auto
  -- `r.electionElapsed++`
  wp_apply raft.wp_load_electionElapsed $$ Hphys as %v Hphys
  wp_apply raft.wp_store_electionElapsed $$ Hphys as Hphys
  -- `r.promotable() && r.pastElectionTimeout()`
  wp_apply wp_promotable cfg r id s $$ [$Hphys] as %b ⟨Hphys, -⟩
  wp_if_destruct
  all_goals try (
    wp_apply wp_pastElectionTimeout cfg r id s $$ [$Hphys] as %b2 Hphys
    wp_if_destruct)
  -- the campaign: `r.electionElapsed = 0`, `r.Step(pb.Message{From: r.id, Type: MsgHup})`
  all_goals try (
    wp_apply raft.wp_store_electionElapsed $$ Hphys as Hphys
    wp_apply raft.wp_load_id $$ Hphys as Hphys
    try wp_auto
    have hP : (W32 0 : w32) ≠ MsgProp := by simp [MsgProp]
    imod rdCred_zero_upd (GF := GF) γ with Hcr
    wp_apply wp_raft_Step cfg γ r id s ps _ [] [] Hcfg
      (by simp [StepMsg, stepMsgTypes, MsgHup])
      (by intro h; simp [MsgHup, MsgSnap] at h)
      (fun _ => ⟨rfl, Hterm⟩)
      (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne)
      (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne)
      (by msg_ne) (by msg_ne) (by msg_ne) (RestMsgOk.of_ne ⟨by msg_ne, by msg_ne, by msg_ne, by msg_ne, by msg_ne⟩) Hrel
      $$ [$Hphys $Hghost Hcr]
    · simp only [hP, ↓reduceIte, named]
      isplitr
      · isplitr
        · iapply ownSlice_nil
        isplitr
        · iapply ownSliceCap_nil
        isplitr
        · ipureintro; msg_ne
        isplitr
        · ipureintro; msg_ne
        imodintro
        iintro %ty %Hty
        rw [show mtypeOf (W32 0) = none from rfl] at Hty
        cases Hty
      isplitr
      · iapply ownSlice_nil
      isplitl [Hcr]
      · rw [if_neg (by msg_ne)]; iexact Hcr
      imodintro
      iintro %Hc
      simp [MsgSnap] at Hc
    simp only [hP, ↓reduceIte]
    iintro %err %s' %ps' ⟨Hphys, Hghost, %Hrel', %Href, -, %Hfr, %Htm, -, Herr⟩
    icases Herr with (%Herr | ⟨%Hc', -⟩)
    · subst Herr
      wp_auto
      iapply HΦ $$ %s' %ps'
      iframe Hphys Hghost
      ipureintro
      obtain ⟨Ht1, Ht2, -, Hi, -⟩ := Htm (by msg_ne)
      exact ⟨Hrel', Href, Hfr (by msg_ne) (by msg_ne), Ht1, Ht2 rfl, Hi (by msg_ne)⟩
    · exfalso; revert Hc'; msg_ne)
  -- no campaign: nothing changed
  all_goals (
    try wp_auto
    iapply HΦ $$ %s %ps
    iframe Hphys Hghost
    ipureintro
    exact ⟨Hrel, ⟨[], .refl _⟩, TickStep.refl s⟩)

end proof

end EtcdGrove
end Perennial
