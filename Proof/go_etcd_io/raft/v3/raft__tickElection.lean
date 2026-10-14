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

/-- `electionElapsed++`, then possibly the campaign: `raft.Step` of a `MsgHup`, in the ghost
mode `md` (2026-10-14, stage B7 part 2), which a `MsgHup` keeps (`GMode.StepOut.keep`). -/
theorem raft.tickElection.wp_proof
    (wp_promotable : raft.promotable.spec (GF := GF) (hG := hG))
    (wp_pastElectionTimeout : raft.pastElectionTimeout.spec (GF := GF) (hG := hG))
    (wp_raft_Step : raft.Step.spec (GF := GF) (hG := hG)) :
    raft.tickElection.spec (GF := GF) (hG := hG) := by
  intro c md γ r id s Hterm Hwf Hpc
  wp_start as H
  iNamed H
  wp_auto
  -- `r.electionElapsed++`
  wp_apply raft.wp_load_electionElapsedC $$ Hphys as %v Hphys
  wp_apply raft.wp_store_electionElapsedC $$ Hphys as Hphys
  -- `r.promotable() && r.pastElectionTimeout()`
  wp_apply wp_promotable c r id s $$ [$Hphys] as %b ⟨Hphys, -⟩
  wp_if_destruct
  all_goals try (
    wp_apply wp_pastElectionTimeout c r id s $$ [$Hphys] as %b2 Hphys
    wp_if_destruct)
  -- the campaign: `r.electionElapsed = 0`, `r.Step(pb.Message{From: r.id, Type: MsgHup})`
  all_goals try (
    wp_apply raft.wp_store_electionElapsedC $$ Hphys as Hphys
    wp_apply raft.wp_load_idC $$ Hphys as Hphys
    try wp_auto
    have hP : (W32 0 : w32) ≠ MsgProp := by simp [MsgProp]
    imod rdCred_zero_upd (GF := GF) γ with Hcr
    wp_apply wp_raft_Step c md γ r id s _ [] []
      (by simp [StepMsg, stepMsgTypes, MsgHup])
      (by intro h; simp [MsgHup, MsgSnap] at h)
      (fun _ => ⟨rfl, Hterm⟩)
      (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne)
      (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne)
      (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne)
      (RestMsgOk.of_ne ⟨by msg_ne, by msg_ne, by msg_ne, by msg_ne, by msg_ne⟩) Hwf
      (GMode.Pre.of_other (by msg_ne) Hpc (by msg_ne) (by msg_ne))
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
    iintro %err %s' %c' %md' ⟨Hphys, Hghost, %Hwf', %Href, %Hc', -, %Hfr, %Htm, -, Herr⟩
    have Hcm := Href.commit_mono
    have e1 := Href.keep (by msg_ne); subst e1
    have e2 := Hc' (by msg_ne); subst e2
    icases Herr with (%Herr | ⟨%Hc'', -⟩)
    · subst Herr
      wp_auto
      iapply HΦ $$ %s'
      iframe Hphys Hghost
      ipureintro
      obtain ⟨Ht1, Ht2, -, Hi, -⟩ := Htm (by msg_ne)
      exact ⟨Hwf', Hcm, Hfr (by msg_ne) (by msg_ne), Ht1, Ht2 rfl, Hi (by msg_ne)⟩
    · exfalso; revert Hc''; msg_ne)
  -- no campaign: nothing changed
  all_goals (
    try wp_auto
    iapply HΦ $$ %s
    iframe Hphys Hghost
    ipureintro
    exact ⟨Hwf, Int.le_refl _, TickStep.refl s⟩)

end proof

end EtcdGrove
end Perennial
