/- Lean-first (no Rocq counterpart). -/
module

public import Spec.go_etcd_io.raft.v3.raftpb.MessageType__Enum
public import Proof.go_etcd_io.raft.v3.InvPbMsg
public import Spec.go_etcd_io.raft.v3.raft__tickHeartbeat
public import Spec.go_etcd_io.raft.v3.raft__abortLeaderTransfer

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

/-- A premise of `Step` about another message type: `MsgBeat` is not it. -/
local macro "msg_ne" : tactic => `(tactic| (intro Hc; simp [MsgHup, MsgVote, MsgVoteResp,
  MsgPreVote, MsgPreVoteResp, MsgApp, MsgHeartbeat, MsgAppResp, MsgHeartbeatResp, MsgSnap,
  MsgBeat, MsgProp, MsgStorageAppendResp, MsgStorageApplyResp, MsgReadIndex,
  MsgReadIndexResp, MsgForgetLeader, MsgUnreachable, MsgSnapStatus, MsgTimeoutNow, MsgTransferLeader] at Hc))

/-- The two counters; past the election timeout the counter is reset (`checkQuorum` is
off) and (2026-10-13) a leader's leader transfer is aborted (`abortLeaderTransfer`, which
the protocol does not see: the state after it, `s1`, is `s` with `lt := 0`); then for a
leader past the heartbeat timeout `raft.Step` of a `MsgBeat`. -/
theorem raft.tickHeartbeat.wp_proof
    (wp_raft_Step : raft.Step.spec (GF := GF) (hG := hG))
    (wp_raft_abortLeaderTransfer : raft.abortLeaderTransfer.spec (GF := GF) (hG := hG))
    (wp_MessageType_Enum : raftpb.MessageType.Enum.spec (GF := GF) (hG := hG)) :
    raft.tickHeartbeat.spec (GF := GF) (hG := hG) := by
  intro c md γ r id s Hwf Hpc
  wp_start as H
  iNamed H
  wp_auto_lc 1
  -- `r.heartbeatElapsed++`, `r.electionElapsed++`
  wp_apply raft.wp_load_heartbeatElapsedC $$ Hphys as %v1 Hphys
  wp_apply raft.wp_store_heartbeatElapsedC $$ Hphys as Hphys
  wp_apply raft.wp_load_electionElapsedC $$ Hphys as %v2 Hphys
  wp_apply raft.wp_store_electionElapsedC $$ Hphys as Hphys
  wp_apply raft.wp_load_electionElapsedC $$ Hphys as %v3 Hphys
  wp_apply raft.wp_load_electionTimeoutC $$ Hphys as %v4 ⟨Hphys, -⟩
  -- the election-timeout block, joined at the state `s1` it leaves
  wp_join iprop(∃ (s1 : NState), "Hphys" ∷ ownRaftPhysCV c c.voters r id s1 ∗
      "Hghost" ∷ ownStepGhost γ md c id s1 ∗
      "%Hs1" ∷ ⌜NStateWf s1 ∧ s1.role = s.role ∧
        uint.Z s.logst.committed ≤ uint.Z s1.logst.committed ∧
        (∀ s', TickStep s1 s' → TickStep s s')⌝ ∗
      "r" ∷ r_ptr ↦ r) with [Hphys Hghost r] as ⟨%s1, Hphys, Hghost, %Hs1, r⟩
  · wp_apply raft.wp_store_electionElapsedC $$ Hphys as Hphys
    wp_apply raft.wp_load_checkQuorumC $$ Hphys as Hphys
    try wp_auto
    wp_apply raft.wp_load_stateC $$ Hphys as Hphys
    cases Hrole : s.role
    all_goals simp (config := { decide := true }) only [
      decide_false, _root_.decide_true]
    all_goals try wp_auto
    rotate_left 2
    · -- a leader: abort a transfer in progress
      wp_apply raft.wp_load_leadTransfereeC $$ Hphys as Hphys
      by_cases Hlt : s.lt = W64 0
      · rw [decide_eq_true Hlt]
        try wp_auto
        wp_join_done
        iexists s
        iframe
        ipureintro
        exact ⟨Hwf, Hrole, Int.le_refl _, fun _ h => h⟩
      · rw [decide_eq_false Hlt]
        try wp_auto
        wp_apply wp_raft_abortLeaderTransfer c (V := c.voters) $$ [$Hphys] as Hphys
        try wp_auto
        wp_join_done
        ihave Hghost := ownStepGhost_congr γ md c id (s := s) (s' := { s with lt := W64 0 }) rfl rfl rfl rfl $$ Hghost
        iexists { s with lt := W64 0 }
        iframe
        ipureintro
        exact ⟨Hwf, Hrole, Int.le_refl _, fun _ h => h⟩
    all_goals
      wp_join_done
      iexists s
      iframe
      ipureintro
      exact ⟨Hwf, Hrole, Int.le_refl _, fun _ h => h⟩
  · iexists s
    iframe
    ipureintro
    exact ⟨Hwf, rfl, Int.le_refl _, fun _ h => h⟩
  obtain ⟨Hwf1, Hrole1, Hcm1, Htr⟩ := Hs1
  -- `if r.state != StateLeader { return }`
  wp_apply raft.wp_load_stateC $$ Hphys as Hphys
  cases Hrole : s1.role
  all_goals
    simp (config := { decide := true }) only [
      decide_false, _root_.decide_true]
    try wp_auto
  all_goals try (
    iapply HΦ $$ %s1
    iframe Hphys Hghost
    ipureintro
    exact ⟨Hwf1, Hcm1, Htr _ (TickStep.refl s1)⟩)
  -- a leader: past the heartbeat timeout, `r.heartbeatElapsed = 0` and
  -- `r.Step(pb.Message{From: r.id, Type: MsgBeat})`
  wp_apply raft.wp_load_heartbeatElapsedC $$ Hphys as %v5 Hphys
  wp_apply raft.wp_load_heartbeatTimeoutC $$ Hphys as %v6 Hphys
  by_cases Hhb : sint.Z v6 ≤ sint.Z v5
  · rw [decide_eq_true Hhb]
    wp_auto
    wp_apply raft.wp_store_heartbeatElapsedC $$ Hphys as Hphys
    wp_apply raft.wp_load_idC $$ Hphys as Hphys
    try wp_auto
    -- (raft v3.7, stage R4) `&pb.Message{From: new(r.id), Type: pb.MsgBeat.Enum()}`, built into
    -- `msgIn` (`msgPtsC_of_struct`), its two cells frozen
    rw [show raftpb.MsgBeat = #((W32 1 : raftpb.MessageType)) from rfl]
    -- (as `confchange/toConfChangeSingle.lean`) Perennial gives `NotInterface` per type
    -- constructor, and `go.int32` (`MessageType`'s underlying type) is a non-reducible definition
    haveI : go.NotInterface go.int32 := ⟨by unfold go.int32; trivial⟩
    wp_apply wp_MessageType_Enum (W32 1)
    iintro %pty Hpty
    imod cellRO_alloc $$ Hpty with #cTy
    imod cellRO_alloc $$ «$v0» with #cFr
    wp_auto
    ihave Hnilb : (slice.nil ↦* ([] : List w8) : IProp GF) $$ []
    · iapply ownSlice_nil
    imod ownSlice_persist $$ Hnilb with #Hnilb
    ihave Hnile : (slice.nil ↦* ([] : List Loc) : IProp GF) $$ []
    · iapply ownSlice_nil
    imod ownSlice_persist $$ Hnile with #Hnile
    ihave Hnilr : (slice.nil ↦* ([] : List Loc) : IProp GF) $$ []
    · iapply ownSlice_nil
    imod msgPtsC_of_struct «$a0_ptr»
        { state' := zeroValDef, Type' := pty, To' := null, From' := «$v0_ptr», Term' := null,
          LogTerm' := null, Index' := null, Entries' := slice.nil, Commit' := null, Vote' := null,
          Snapshot' := null, Reject' := null, RejectHint' := null, Context' := slice.nil,
          Responses' := slice.nil, unknownFields' := slice.nil, sizeCache' := 0 }
        DFrac.discard true [] ⟨{ (zero_val MessageM) with Type' := W32 1, From' := id }, [], none, [], []⟩
        ⊤ rfl $$ [«$a0» Hnilr] with Hmsg
    · iframe «$a0» Hnile Hnilb Hnilr cTy cFr
      simp only [snapOpt, ↓reduceIte]
      repeat (isplitr; · iunfold cellRO; ileft; ipureintro; exact ⟨rfl, rfl⟩)
      isplitr
      · iapply BigSepL2.bigSepL2_nil.2; itrivial
      isplitr
      · iapply ownSliceCap_nil
      itrivial
    have hP : (W32 1 : w32) ≠ MsgProp := by simp [MsgProp]
    imod rdCred_zero_upd (GF := GF) γ with Hcr
    wp_apply wp_raft_Step c md γ r id s1 «$a0_ptr»
        ({ (zero_val MessageM) with Type' := W32 1, From' := id } : MessageM) [] [] none []
        (by simp [StepMsg, stepMsgTypes, MsgBeat])
        (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne)
        (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (fun _ => rfl) (by msg_ne)
        (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne)
        (RestMsgOk.of_ne ⟨by msg_ne, by msg_ne, by msg_ne, by msg_ne, by msg_ne⟩) Hwf1
        (GMode.Pre.of_other (by msg_ne) (fun h => by rw [Hrole1]; exact Hpc h) (by msg_ne) (by msg_ne))
      $$ [$Hphys $Hghost $Hlc1 Hcr Hmsg]
    · simp only [hP, ↓reduceIte, named]
      ihave Hmsg := msgIn_of_msgPtsC_cap _ _ _ $$ Hmsg
      isplitl [Hmsg]
      · iframe Hmsg
        repeat (isplitr; · first | iempintro | (ipureintro; simp) | (ipureintro; msg_ne))
        imodintro
        iintro %ty %Hty
        rw [show mtypeOf (W32 1) = none from rfl] at Hty
        cases Hty
      isplitl [Hcr]
      · rw [ite_eq_right (by msg_ne)]; iexact Hcr
      imodintro
      iintro %Hc
      simp [MsgSnap] at Hc
    simp only [hP]
    iintro %err %s' %c' %md' ⟨Hphys, Hghost, %Hwf', %Href, %Hcc, -, %Hfr, %Htm, -, Herr⟩
    have Hcm := Href.commit_mono
    have e1 := Href.keep (by msg_ne) (by msg_ne); subst e1
    have e2 := Hcc (by msg_ne); subst c'
    icases Herr with (%Herr | ⟨%Hc', -⟩)
    · subst Herr
      wp_auto
      iapply HΦ $$ %s'
      iframe Hphys Hghost
      ipureintro
      obtain ⟨Ht1, -, Ht3, Hi, -⟩ := Htm (by msg_ne)
      have Ht3 := Ht3 (by msg_ne) (by msg_ne) (by msg_ne)
      have H0 : uint.Z (zero_val MessageM).Term' = 0 := rfl
      simp only [H0] at Ht3
      exact ⟨Hwf', Int.le_trans Hcm1 Hcm, Htr _ ⟨Hfr (by msg_ne) (by msg_ne), Ht1,
        by have h0 : 0 ≤ uint.Z s1.term := by word
           rw [Int.max_eq_left h0] at Ht3; omega,
        Hi (by msg_ne)⟩⟩
    · exfalso; revert Hc'; msg_ne
  · rw [decide_eq_false Hhb]
    wp_auto
    iapply HΦ $$ %s1
    iframe Hphys Hghost
    ipureintro
    exact ⟨Hwf1, Hcm1, Htr _ (TickStep.refl s1)⟩

end proof

end EtcdGrove
end Perennial
