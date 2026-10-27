/- Lean-first (no Rocq counterpart). -/
module

public import Spec.go_etcd_io.raft.v3.raftpb.MessageType__Enum
public import Proof.go_etcd_io.raft.v3.InvPbMsg
public import Spec.go_etcd_io.raft.v3.raft__tickElection
public import Spec.go_etcd_io.raft.v3.raft__promotable
public import Spec.go_etcd_io.raft.v3.raft__pastElectionTimeout

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- A premise of `Step` about another message type: `MsgHup` (`W32 0`) is not it. -/
local macro "msg_ne" : tactic => `(tactic| (intro Hc; simp [MsgHup, MsgVote, MsgVoteResp,
  MsgPreVote, MsgPreVoteResp, MsgApp, MsgHeartbeat, MsgAppResp, MsgHeartbeatResp,MsgCheckQuorum, MsgSnap,
  MsgBeat, MsgProp, MsgStorageAppendResp, MsgStorageApplyResp, MsgReadIndex,
  MsgReadIndexResp, MsgForgetLeader, MsgUnreachable, MsgSnapStatus, MsgTimeoutNow, MsgTransferLeader] at Hc))

/-- `electionElapsed++`, then possibly the campaign: `raft.Step` of a `MsgHup`, in the ghost
mode `md` (2026-10-14, stage B7 part 2), which a `MsgHup` keeps (`GMode.StepOut.keep`).
(Raft v3.7, stage R4: the message is `&pb.Message{From: new(r.id), Type: pb.MsgHup.Enum()}`,
built into `msgIn` with `msgPtsC_of_struct`, its two cells frozen; `MsgHup.Enum()` is a new
callee.) -/
theorem raft.tickElection.wp_proof
    (wp_promotable : raft.promotable.spec (GF := GF) (hG := hG))
    (wp_pastElectionTimeout : raft.pastElectionTimeout.spec (GF := GF) (hG := hG))
    (wp_raft_Step : raft.Step.spec (GF := GF) (hG := hG))
    (wp_MessageType_Enum : raftpb.MessageType.Enum.spec (GF := GF) (hG := hG)) :
    raft.tickElection.spec (GF := GF) (hG := hG) := by
  intro c md γ r id s Hterm Htc Hwf Hfla Hpc
  wp_start as H
  iNamed H
  wp_auto_lc 1
  -- `r.electionElapsed++`
  wp_apply raft.wp_load_electionElapsedC $$ Hphys as %v Hphys
  wp_apply raft.wp_store_electionElapsedC $$ Hphys as Hphys
  -- `r.promotable() && r.pastElectionTimeout()`
  wp_apply wp_promotable c r id s $$ [$Hphys] as %b ⟨Hphys, -⟩
  wp_if_destruct
  · -- not promotable: nothing changed
    try wp_auto
    iapply HΦ $$ %s
    iframe Hphys Hghost
    ipureintro
    exact ⟨Hwf, Int.le_refl _, TickStep.refl s⟩
  wp_apply wp_pastElectionTimeout c r id s $$ [$Hphys] as %b2 Hphys
  wp_if_destruct
  · -- the timeout has not passed: nothing changed
    try wp_auto
    iapply HΦ $$ %s
    iframe Hphys Hghost
    ipureintro
    exact ⟨Hwf, Int.le_refl _, TickStep.refl s⟩
  -- the campaign: `r.electionElapsed = 0`, `r.Step(&pb.Message{From: new(r.id), Type:
  -- pb.MsgHup.Enum()})`
  wp_apply raft.wp_store_electionElapsedC $$ Hphys as Hphys
  wp_apply raft.wp_load_idC $$ Hphys as Hphys
  try wp_auto
  rw [show raftpb.MsgHup = #((W32 0 : raftpb.MessageType)) from rfl]
  -- (as `confchange/toConfChangeSingle.lean`) Perennial gives `NotInterface` per type
  -- constructor, and `go.int32` (`MessageType`'s underlying type) is a non-reducible definition
  haveI : go.NotInterface go.int32 := ⟨by unfold go.int32; trivial⟩
  wp_apply wp_MessageType_Enum (W32 0)
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
      DFrac.discard true [] ⟨{ (zero_val MessageM) with Type' := W32 0, From' := id }, [], none, [], []⟩
      ⊤ rfl $$ [«$a0» Hnilr] with Hmsg
  · iframe «$a0» Hnile Hnilb Hnilr cTy cFr
    simp only [snapOpt, ↓reduceIte]
    repeat (isplitr; · iunfold cellRO; ileft; ipureintro; exact ⟨rfl, rfl⟩)
    isplitr
    · iapply BigSepL2.bigSepL2_nil.2; itrivial
    isplitr
    · iapply ownSliceCap_nil
    itrivial
  have hP : (W32 0 : w32) ≠ MsgProp := by simp [MsgProp]
  imod rdCred_zero_upd (GF := GF) γ with Hcr
  wp_apply wp_raft_Step c md γ r id s «$a0_ptr»
      ({ (zero_val MessageM) with Type' := W32 0, From' := id } : MessageM) [] [] none []
      (by simp [StepMsg, stepMsgTypes, MsgHup])
      (fun _ => ⟨rfl, Hterm, Htc, Hfla⟩)
      (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne)
      (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne)
      (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne)
      (RestMsgOk.of_ne ⟨by msg_ne, by msg_ne, by msg_ne, by msg_ne, by msg_ne⟩) Hwf
      (GMode.Pre.of_other (by msg_ne) Hpc (by msg_ne) (by msg_ne))
      (fun h => absurd h (by msg_ne))
    $$ [$Hphys $Hghost $Hlc1 Hcr Hmsg]
  · simp only [hP, ↓reduceIte, named]
    ihave Hmsg := msgIn_of_msgPtsC_cap _ _ _ $$ Hmsg
    isplitl [Hmsg]
    · iframe Hmsg
      repeat (isplitr; · first | iempintro | (ipureintro; simp) | (ipureintro; msg_ne))
      imodintro
      iintro %ty %Hty
      rw [show mtypeOf (W32 0) = none from rfl] at Hty
      cases Hty
    isplitl [Hcr]
    · rw [ite_eq_right (by msg_ne)]; iexact Hcr
    imodintro
    iintro %Hc
    simp [MsgSnap] at Hc
  iintro %err %s' %c' %md' ⟨Hphys, Hghost, %Hwf', %Href, %Hc', -, %Hfr, %Htm, -, -, -, Herr⟩
  have Hcm := Href.commit_mono
  have e1 := Href.keep (by msg_ne) (by msg_ne); subst e1
  have e2 := Hc' (by msg_ne); subst c'
  icases Herr with (%Herr | ⟨%Hc'', -⟩)
  · subst Herr
    wp_auto
    iapply HΦ $$ %s'
    iframe Hphys Hghost
    ipureintro
    have Htm' := Htm (by msg_ne)
    obtain ⟨Ht1, Ht2, -, Hi, -, Hpc'⟩ := Htm (by msg_ne)
    exact ⟨Hwf', Hcm, Hfr (by msg_ne) (by msg_ne) (fun h => absurd h (by msg_ne)), Ht1, Ht2 rfl, Hi (by msg_ne),
      fun h => (Hpc' h).1, fun _ hg => PreGuardF.step Htm' hg⟩
  · exfalso; revert Hc''; msg_ne

end proof

end EtcdGrove
end Perennial
