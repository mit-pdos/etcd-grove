/- Lean-first (no Rocq counterpart). -/
module

public import Spec.go_etcd_io.raft.v3.raft__tickHeartbeat

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

/-- A premise of `Step` about another message type: `MsgBeat` is not it. -/
local macro "msg_ne" : tactic => `(tactic| (intro Hc; simp [MsgHup, MsgVote, MsgVoteResp,
  MsgPreVote, MsgPreVoteResp, MsgApp, MsgHeartbeat, MsgAppResp, MsgHeartbeatResp, MsgSnap,
  MsgBeat, MsgProp, MsgStorageAppendResp, MsgStorageApplyResp] at Hc))

/-- The two counters, the election-timeout reset (`checkQuorum` and leader transfer are
off), then for a leader past the heartbeat timeout `raft.Step` of a `MsgBeat`. -/
theorem raft.tickHeartbeat.wp_proof
    (wp_raft_Step : raft.Step.spec (GF := GF) (hG := hG)) :
    raft.tickHeartbeat.spec (GF := GF) (hG := hG) := by
  intro cfg γ r id s ps Hcfg Hin Hrel
  wp_start as H
  iNamed H
  wp_auto
  -- `r.heartbeatElapsed++`, `r.electionElapsed++`
  wp_apply raft.wp_load_heartbeatElapsed $$ Hphys as %v1 Hphys
  wp_apply raft.wp_store_heartbeatElapsed $$ Hphys as Hphys
  wp_apply raft.wp_load_electionElapsed $$ Hphys as %v2 Hphys
  wp_apply raft.wp_store_electionElapsed $$ Hphys as Hphys
  wp_apply raft.wp_load_electionElapsed $$ Hphys as %v3 Hphys
  wp_apply raft.wp_load_electionTimeout $$ Hphys as %v4 ⟨Hphys, -⟩
  -- past the election timeout: reset the counter; `checkQuorum` is off, and a leader has
  -- no transfer in progress
  cases Hrole : s.role
  all_goals by_cases Hge : sint.Z v4 ≤ sint.Z v3
  all_goals first | rw [decide_eq_true Hge] | rw [decide_eq_false Hge]
  all_goals wp_auto
  all_goals try (
    wp_apply raft.wp_store_electionElapsed $$ Hphys as Hphys
    wp_apply raft.wp_load_checkQuorum $$ Hphys as Hphys
    wp_apply raft.wp_load_state $$ Hphys as Hphys
    simp (config := { decide := true }) only [Hrole, stateW64, StateFollower,
      StateCandidate, StateLeader, StatePreCandidate, decide_false, decide_true]
    try wp_auto
    try (wp_apply raft.wp_load_leadTransferee $$ Hphys as Hphys))
  -- `if r.state != StateLeader { return }`
  all_goals (
    wp_apply raft.wp_load_state $$ Hphys as Hphys
    simp (config := { decide := true }) only [Hrole, stateW64, StateFollower,
      StateCandidate, StateLeader, StatePreCandidate, decide_false, decide_true]
    try wp_auto)
  all_goals try (
    iapply HΦ $$ %s %ps
    iframe Hphys Hghost
    ipureintro
    exact ⟨Hrel, ⟨[], .refl _⟩, TickStep.refl s⟩)
  -- a leader: past the heartbeat timeout, `r.heartbeatElapsed = 0` and
  -- `r.Step(pb.Message{From: r.id, Type: MsgBeat})`
  all_goals (
    wp_apply raft.wp_load_heartbeatElapsed $$ Hphys as %v5 Hphys
    wp_apply raft.wp_load_heartbeatTimeout $$ Hphys as %v6 Hphys
    by_cases Hhb : sint.Z v6 ≤ sint.Z v5
    · rw [decide_eq_true Hhb]
      wp_auto
      wp_apply raft.wp_store_heartbeatElapsed $$ Hphys as Hphys
      wp_apply raft.wp_load_id $$ Hphys as Hphys
      try wp_auto
      have hP : (W32 1 : w32) ≠ MsgProp := by simp [MsgProp]
      wp_apply wp_raft_Step cfg γ r id s ps _ [] [] Hcfg
        (by simp [StepMsg, stepMsgTypes, MsgBeat]) Hin
        (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne)
        (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (fun _ => rfl) (by msg_ne)
        (by msg_ne) (by msg_ne) Hrel
        $$ [$Hphys $Hghost]
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
          rw [show mtypeOf (W32 1) = none from rfl] at Hty
          cases Hty
        isplitr
        · itrivial
        isplitr
        · iexists []
          isplitr
          · iapply ownSlice_nil
          ipureintro
          exact ⟨by simp [campaignTransfer], fun Hc => by simp [MsgHeartbeatResp] at Hc⟩
        imodintro
        iintro %Hc
        simp [MsgSnap] at Hc
      simp only [hP, ↓reduceIte]
      iintro %err %s' %ps' ⟨Hphys, Hghost, %Hrel', %Href, -, %Hfr, %Htm, Herr, -⟩
      icases Herr with (%Herr | ⟨%Hc', -⟩)
      · subst Herr
        wp_auto
        iapply HΦ $$ %s' %ps'
        iframe Hphys Hghost
        ipureintro
        obtain ⟨Ht1, -, Ht3, Hi⟩ := Htm (by msg_ne)
        have Ht3 := Ht3 (by msg_ne) (by msg_ne)
        have H0 : uint.Z (0 : w64) = 0 := rfl
        simp only [H0] at Ht3
        exact ⟨Hrel', Href, Hfr (by msg_ne) (by msg_ne), Ht1,
          by have h0 : 0 ≤ uint.Z s.term := by word
             rw [Int.max_eq_left h0] at Ht3; omega,
          Hi (by msg_ne)⟩
      · exfalso; revert Hc'; msg_ne
    · rw [decide_eq_false Hhb]
      wp_auto
      iapply HΦ $$ %s %ps
      iframe Hphys Hghost
      ipureintro
      exact ⟨Hrel, ⟨[], .refl _⟩, TickStep.refl s⟩)

end proof

end EtcdGrove
end Perennial
