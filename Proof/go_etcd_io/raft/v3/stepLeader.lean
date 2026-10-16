/-
Port of `election_proof/proof_stepLeader.v`: the main theorem, by the message type, over the
branches of `stepLeader/Rest.lean` and `stepLeader/MsgProp.lean` (raft v3.7, stage R4).
-/
module

public import Proof.go_etcd_io.raft.v3.stepLeader.Rest
public import Proof.go_etcd_io.raft.v3.stepLeader.MsgProp

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- By the message type, one lemma each. The non-`MsgProp` lemmas are stated at
`LeaderNonpropResult` with `err = nil`; `HΦ'` turns that into the postcondition with
`dropped = false`.

raft v3.7 (2026-10-15, stage R4): the message is `Step`'s `msgIn` (`"Hm"`), handed to the
lemma of its type, which reads it by its getters (callees); a `MsgReadIndex` freezes it
(`msgPtsC_to_msgOwn`, `msgOwn_persist`) to keep it pending or answer it; the batch of a
`MsgProp` no longer comes back. -/
theorem stepLeader.wp_proof
    (wp_raft_bcastHeartbeat : raft.bcastHeartbeat.spec (GF := GF) (hG := hG))
    (wp_raft_sendAppend : raft.sendAppend.spec (GF := GF) (hG := hG))
    (wp_raft_maybeSendAppend : raft.maybeSendAppend.spec (GF := GF) (hG := hG))
    (wp_raft_bcastAppend : raft.bcastAppend.spec (GF := GF) (hG := hG))
    (wp_raft_appendEntry : raft.appendEntry.spec (GF := GF) (hG := hG))
    (wp_raft_maybeCommit : raft.maybeCommit.spec (GF := GF) (hG := hG))
    (wp_releasePendingReadIndexMessages :
      releasePendingReadIndexMessages.spec (GF := GF) (hG := hG))
    (wp_Progress_MaybeUpdate : tracker.Progress.MaybeUpdate.spec (GF := GF) (hG := hG))
    (wp_Progress_MaybeDecrTo : tracker.Progress.MaybeDecrTo.spec (GF := GF) (hG := hG))
    (wp_Progress_BecomeProbe : tracker.Progress.BecomeProbe.spec (GF := GF) (hG := hG))
    (wp_Progress_BecomeReplicate :
      tracker.Progress.BecomeReplicate.spec (GF := GF) (hG := hG))
    (wp_Progress_CanBumpCommit : tracker.Progress.CanBumpCommit.spec (GF := GF) (hG := hG))
    (wp_Inflights_FreeLE : tracker.Inflights.FreeLE.spec (GF := GF) (hG := hG))
    (wp_raftLog_findConflictByTerm : raftLog.findConflictByTerm.spec (GF := GF) (hG := hG))
    (wp_raftLog_lastIndex : raftLog.lastIndex.spec (GF := GF) (hG := hG))
    (wp_raftLog_firstIndex : raftLog.firstIndex.spec (GF := GF) (hG := hG))
    (wp_raft_committedEntryInCurrentTerm :
      raft.committedEntryInCurrentTerm.spec (GF := GF) (hG := hG))
    (wp_sendMsgReadIndexResponse : sendMsgReadIndexResponse.spec (GF := GF) (hG := hG))
    (wp_readOnly_recvAck : readOnly.recvAck.spec (GF := GF) (hG := hG))
    (wp_readOnly_maybeAdvance : readOnly.maybeAdvance.spec (GF := GF) (hG := hG))
    (wp_raft_responseToReadIndexReq : raft.responseToReadIndexReq.spec (GF := GF) (hG := hG))
    (wp_raft_send : raft.send.spec (GF := GF) (hG := hG))
    (wp_raft_sendTimeoutNow : raft.sendTimeoutNow.spec (GF := GF) (hG := hG))
    (wp_raft_abortLeaderTransfer : raft.abortLeaderTransfer.spec (GF := GF) (hG := hG))
    (wp_UnmarshalConfChange : proto.UnmarshalConfChange.spec (GF := GF) (hG := hG))
    (wp_UnmarshalConfChangeV2 : proto.UnmarshalConfChangeV2.spec (GF := GF) (hG := hG))
    (wp_ConfChange_AsV2 : raftpb.ConfChange.AsV2.spec (GF := GF) (hG := hG))
    (wp_ConfChangeV2_AsV2 : raftpb.ConfChangeV2.AsV2.spec (GF := GF) (hG := hG))
    (wp_fmt_Sprintf : fmt.Sprintf.spec (GF := GF) (hG := hG))
    (wp_traceChangeConfEvent : traceChangeConfEvent.spec (GF := GF) (hG := hG))
    (wp_GetType : raftpb.Message.GetType.spec (GF := GF) (hG := hG))
    (wp_GetFrom : raftpb.Message.GetFrom.spec (GF := GF) (hG := hG))
    (wp_GetReject : raftpb.Message.GetReject.spec (GF := GF) (hG := hG))
    (wp_GetIndex : raftpb.Message.GetIndex.spec (GF := GF) (hG := hG))
    (wp_GetRejectHint : raftpb.Message.GetRejectHint.spec (GF := GF) (hG := hG))
    (wp_GetLogTerm : raftpb.Message.GetLogTerm.spec (GF := GF) (hG := hG))
    (wp_GetContext : raftpb.Message.GetContext.spec (GF := GF) (hG := hG))
    (wp_GetTo : raftpb.Message.GetTo.spec (GF := GF) (hG := hG))
    (wp_Entry_GetType : raftpb.Entry.GetType.spec (GF := GF) (hG := hG))
    (wp_Entry_GetData : raftpb.Entry.GetData.spec (GF := GF) (hG := hG))
    (wp_EntryType_Enum : raftpb.EntryType.Enum.spec (GF := GF) (hG := hG))
    (wp_DescribeConfChange : DescribeConfChange.spec (GF := GF) (hG := hG)) :
    stepLeader.spec (GF := GF) (hG := hG) := by
  intro c r id s ml m ents sn ctx rs Hty Hlead Hfrom0 Hself Hprop Hrdnz Hri Hhr Hack
  iintro %Φ ⟨#Hinit, Hphys, Hm, Hcc⟩ HΦ
  -- a leader is a voter (`ownRaftPhys`'s `Hvoter`; until 2026-10-13 a premise)
  icases ownRaftPhysC_voter c r id s $$ Hphys with ⟨%Hvoter, Hphys⟩
  have Hid : id ∈ c.voters := Hvoter (by rw [Hlead]; decide)
  by_cases Hp : m.Type' = MsgProp
  · obtain ⟨Hne, Hsmall, Hnz⟩ := Hprop Hp
    icases Hcc $$ %Hp with ⟨%cs, #Hcc⟩
    rw [show (if m.Type' = MsgProp then DFrac.own 1 else DFrac.discard) = DFrac.own 1 from
      if_pos Hp]
    iapply wp_stepLeader_prop c wp_raft_bcastAppend wp_raft_appendEntry wp_raftLog_lastIndex
      wp_UnmarshalConfChange wp_UnmarshalConfChangeV2 wp_ConfChange_AsV2 wp_ConfChangeV2_AsV2
      wp_fmt_Sprintf wp_traceChangeConfEvent wp_GetType wp_Entry_GetType
      wp_Entry_GetData wp_EntryType_Enum wp_DescribeConfChange r id s ml m ents sn ctx rs cs Hp Hid
      Hne Hsmall Hnz $$ [Hphys Hm]
    · iframe
      iframe Hinit Hcc
    inext
    iintro %err %s' %dropped ⟨Hphys, %Hres, Herr⟩
    iapply HΦ
    iframe Hphys Herr
    ipureintro
    simp only [LeaderStepResultC, Hp, ↓reduceIte]
    exact Hres
  ihave HΦ' : iprop(▷ ∀ (err : GoInterface) (s' : NState),
      ownRaftPhysCV c c.voters r id s' ∗ ⌜err = interface.nil⌝ ∗
      ⌜LeaderNonpropResultC c id s m ents ctx s'⌝ -∗ Φ #err) $$ [HΦ]
  · inext
    iintro %err %s' ⟨Hphys, %Herr, %Hres⟩
    iapply HΦ $$ %err %s' %false
    iframe Hphys
    isplitr
    · ipureintro
      simp only [LeaderStepResultC, Hp, ↓reduceIte]
      exact ⟨trivial, Hres⟩
    · simp only [Bool.false_eq_true, ↓reduceIte]
      ipureintro; exact Herr
  rcases Hty with Hty | Hty | Hty | Hty | Hty | Hty | Hty | Hty | Hty | Hty | Hty | Hty | Hty |
    Hty | Hty
  rotate_right 6
  · iapply wp_stepLeader_noop c wp_GetType wp_GetFrom r id s ml m ents ctx sn rs _ _ _
      (Or.inr (Or.inr (Or.inr (Or.inr Hty)))) $$ [Hphys Hm] HΦ'
    iframe
    iexact Hinit
  · iapply wp_stepLeader_rest0 c wp_GetType wp_GetFrom r id s ml m ents ctx sn rs _ _ _
      (Or.inl Hty) $$ [Hphys Hm] HΦ'
    iframe
    iexact Hinit
  · iapply wp_stepLeader_rest0 c wp_GetType wp_GetFrom r id s ml m ents ctx sn rs _ _ _
      (Or.inr Hty) $$ [Hphys Hm] HΦ'
    iframe
    iexact Hinit
  · iapply wp_stepLeader_report c wp_Progress_BecomeProbe wp_GetType wp_GetFrom wp_GetReject
      r id s ml m ents ctx sn rs _ _ _ (Or.inl Hty) $$ [Hphys Hm] HΦ'
    iframe
    iexact Hinit
  · iapply wp_stepLeader_report c wp_Progress_BecomeProbe wp_GetType wp_GetFrom wp_GetReject
      r id s ml m ents ctx sn rs _ _ _ (Or.inr Hty) $$ [Hphys Hm] HΦ'
    iframe
    iexact Hinit
  · iapply wp_stepLeader_transfer c wp_raft_sendAppend wp_raft_sendTimeoutNow
      wp_raftLog_lastIndex wp_raft_abortLeaderTransfer wp_GetType wp_GetFrom
      r id s ml m ents ctx sn rs _ _ _ Hty $$ [Hphys Hm] HΦ'
    iframe
    iexact Hinit
  · iapply wp_stepLeader_noop c wp_GetType wp_GetFrom r id s ml m ents ctx sn rs _ _ _
      (Or.inl Hty) $$ [Hphys Hm] HΦ'
    iframe
    iexact Hinit
  · iapply wp_stepLeader_beat c wp_raft_bcastHeartbeat wp_GetType r id s ml m ents ctx sn rs
      _ _ _ Hty Hlead $$ [Hphys Hm] HΦ'
    iframe
    iexact Hinit
  · obtain ⟨Hclen, Hcb⟩ := Hhr Hty
    iapply wp_stepLeader_hbresp c wp_raft_sendAppend wp_raftLog_lastIndex wp_readOnly_recvAck
      wp_readOnly_maybeAdvance wp_raft_responseToReadIndexReq wp_raft_send wp_GetType wp_GetFrom
      wp_GetContext wp_GetTo r id s ml m ents ctx sn rs _ _ _ Hty
      (Hself (Or.inl Hty)) Hid (Hrdnz (Or.inl Hty)).1 Hclen Hcb $$ [Hphys Hm] HΦ'
    iframe
    iexact Hinit
  · iapply wp_stepLeader_appresp c wp_raft_sendAppend wp_raft_maybeSendAppend
      wp_raft_bcastAppend wp_raft_maybeCommit wp_releasePendingReadIndexMessages
      wp_Progress_MaybeUpdate wp_Progress_MaybeDecrTo wp_Progress_BecomeProbe
      wp_Progress_BecomeReplicate wp_Progress_CanBumpCommit wp_Inflights_FreeLE
      wp_raftLog_findConflictByTerm wp_raftLog_lastIndex wp_raftLog_firstIndex
      wp_raft_sendTimeoutNow wp_GetType wp_GetFrom wp_GetReject wp_GetIndex wp_GetRejectHint
      wp_GetLogTerm r id s ml m Hty Hlead Hid (Hfrom0 Hty) (fun Hr => Hself (Or.inr ⟨Hty, Hr⟩))
      (Hrdnz (Or.inr (Or.inl Hty))).2 (Hrdnz (Or.inr (Or.inl Hty))).1.2.2 (Hack Hty) ents ctx sn rs _ _ _
      $$ [Hphys Hm] HΦ'
    iframe
    iexact Hinit
  · exact absurd Hty Hp
  · iapply wp_stepLeader_noop c wp_GetType wp_GetFrom r id s ml m ents ctx sn rs _ _ _
      (Or.inr (Or.inl Hty)) $$ [Hphys Hm] HΦ'
    iframe
    iexact Hinit
  · iapply wp_stepLeader_noop c wp_GetType wp_GetFrom r id s ml m ents ctx sn rs _ _ _
      (Or.inr (Or.inr (Or.inl Hty))) $$ [Hphys Hm] HΦ'
    iframe
    iexact Hinit
  · iapply wp_stepLeader_noop c wp_GetType wp_GetFrom r id s ml m ents ctx sn rs _ _ _
      (Or.inr (Or.inr (Or.inr (Or.inl Hty)))) $$ [Hphys Hm] HΦ'
    iframe
    iexact Hinit
  · iapply wp_stepLeader_readindex c
      wp_raft_committedEntryInCurrentTerm wp_sendMsgReadIndexResponse wp_GetType
      r id s ml m ents ctx sn rs _ _ _ Hty Hlead
      (Hrdnz (Or.inr (Or.inr Hty))).2 (Hri Hty) $$ [Hphys Hm] HΦ'
    iframe
    iexact Hinit

end proof

end EtcdGrove
end Perennial
