/-
Port of `election_proof/proof_stepLeader.v`: the main theorem, by the message type, over the
branches of `stepLeader/Rest.lean` and `stepLeader/MsgProp.lean` (raft v3.7, stage R4).
-/
module

public import Proof.go_etcd_io.raft.v3.stepLeader.Rest
public import Proof.go_etcd_io.raft.v3.stepLeader.MsgProp
public import Proof.go_etcd_io.raft.v3.stepLeader.CheckQuorum
public import Proof.go_etcd_io.raft.v3.TracedUntraced

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
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
    (wp_DescribeConfChange : DescribeConfChange.spec (GF := GF) (hG := hG))
    -- (2026-10-17, `CheckQuorum` on) the quorum check
    (wp_ProgressTracker_QuorumActive :
      tracker.ProgressTracker.QuorumActive.spec (GF := GF) (hG := hG))
    (wp_ProgressTracker_Visit : tracker.ProgressTracker.Visit.spec (GF := GF) (hG := hG))
    (wp_raft_becomeFollower : raft.becomeFollower.spec (GF := GF) (hG := hG)) :
    stepLeader.spec (GF := GF) (hG := hG) := by
  -- (Q8 stage 1, slice 9) every arm gated: `send`'s and `maybeCommit`'s one specs, no instance
  intro c r id s ml m ents sn ctx rs k0 G G' Gp1 Gp2 Gc Hty Hlead Htz Hfrom0 Hself Hprop Hrdnz Hri Hhr
    Hack Hncc HiG HiP HiC Hxtr Hltr
  iintro %Φ ⟨#Hinit, Hphys, Hm, Hcc, #Hrc, HG, #Hgbeat, Hgriresp, #Hgrihb, Hgtnow, Hgxapp, #Hnosnap,
    Hgcq, Hgprep, Hgpack, #Hgpapp, Hgsapp, #Hghresp, Hgcommit, #Hgrlresp, #Hgrlhb, #Hgaapp,
    #Hgatnow⟩ HΦ
  -- (2026-10-25, T-M M2c) a leader need not be a voter (removed without `StepDownOnRemoval`); until
  -- then `ownRaftPhys`'s `Hvoter` said it was, and the proposal, heartbeat-response and
  -- append-response paths read it
  by_cases Hp : m.Type' = MsgProp
  · obtain ⟨Hne, Hsmall, Hnz⟩ := Hprop Hp
    icases Hcc $$ %Hp with ⟨%cs, #Hcc⟩
    rw [show (if m.Type' = MsgProp then DFrac.own 1 else DFrac.discard) = DFrac.own 1 from
      if_pos Hp]
    -- (slice 9) the gates at the decoded conf changes `cs`
    ispecialize Hgprep $$ %Hp %cs Hcc
    ispecialize Hgpack $$ %Hp %cs Hcc
    iapply wp_stepLeader_prop c wp_raft_bcastAppend wp_raft_appendEntry wp_raftLog_lastIndex
      wp_UnmarshalConfChange wp_UnmarshalConfChangeV2 wp_ConfChange_AsV2 wp_ConfChangeV2_AsV2
      wp_fmt_Sprintf wp_traceChangeConfEvent wp_GetType wp_Entry_GetType
      wp_Entry_GetData wp_EntryType_Enum wp_DescribeConfChange r id s ml m ents sn ctx rs cs k0 Hp
      Hne Hsmall Hnz Hlead (Hncc Hp) G Gp1 Gp2 HiP $$ [Hphys Hm HG Hgprep Hgpack]
    · iframe Hphys Hm HG Hgprep Hgpack
      iframe Hinit Hcc Hrc Hnosnap
      imodintro
      iintro %to %mm %o %Hto %Hmm HG2
      iapply Hgpapp $$ %Hp %cs %to %mm %o Hcc %Hto %Hmm HG2
    inext
    iintro %err %s' %dropped ⟨Hphys, Hrc', %Hres, Herr, HGr⟩
    iapply HΦ
    iframe Hphys Herr
    isplitl [Hrc']
    · iintro %Hd
      iapply Hrc' $$ %Hd.2
    isplitr [HGr]
    · ipureintro
      simp only [LeaderStepResultC, Hp, ↓reduceIte]
      exact Hres
    have Hncq : ¬ (m.Type' = MsgCheckQuorum ∧ s'.role = .follower) := by
      rintro ⟨h, _⟩
      rw [Hp] at h; exact absurd h (by simp [MsgProp, MsgCheckQuorum])
    cases dropped <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · iright; ileft
      iframe HGr
      ipureintro; exact ⟨Hp, by first | trivial | rfl⟩
    · iright; iright; iright
      iframe HGr
      ipureintro; exact ⟨Hncq, fun h => absurd h.2 (by simp),
        fun h => absurd (Hp.symm.trans h.1) (by simp [MsgProp, MsgAppResp])⟩
  ihave HΦ' : iprop(▷ ∀ (err : GoInterface) (s' : NState),
      ownRaftPhysCV c c.voters r id s' ∗ ⌜err = interface.nil⌝ ∗
      ⌜LeaderNonpropResultC c id s m ents ctx s'⌝ ∗
      ((⌜m.Type' = MsgCheckQuorum ∧ s'.role = .follower⌝ ∗ G' s'.outbox) ∨
       (∃ (b : Bool) (N : w64), ⌜m.Type' = MsgAppResp ∧ m.Reject' = false ∧
          ∃ pvs : GMap w64 Progress, prvalsMatch pvs = appRespMatch s m.From' m.Index' ∧
            maybeCommitOut c { s with prvals := pvs } b N⌝ ∗ Gc b N s'.outbox) ∨
       (⌜¬ (m.Type' = MsgCheckQuorum ∧ s'.role = .follower) ∧
          ¬ (m.Type' = MsgAppResp ∧ m.Reject' = false ∧ AppRespRan s m.From' m.Index')⌝ ∗
        G s'.outbox)) -∗ Φ #err) $$ [HΦ]
  · inext
    iintro %err %s' ⟨Hphys, %Herr, %Hres, HR⟩
    iapply HΦ $$ %err %s' %false
    iframe Hphys
    isplitr
    · iintro %Hd; exact absurd Hd.1 Hp
    isplitr [HR]
    · ipureintro
      simp only [LeaderStepResultC, Hp, ↓reduceIte]
      exact ⟨trivial, Hres⟩
    isplitr [HR]
    · simp only [Bool.false_eq_true, ↓reduceIte]
      ipureintro; exact Herr
    -- (slice 9) into the four-way result (no proposal here)
    icases HR with (HR | HR | ⟨%h, HG⟩)
    · ileft; iexact HR
    · iright; iright; ileft; iexact HR
    · iright; iright; iright
      iframe HG
      ipureintro; exact ⟨h.1, fun h' => Hp h'.1, h.2⟩
  by_cases Hcq : m.Type' = MsgCheckQuorum
  · -- (2026-10-17) `MsgCheckQuorum`
    ispecialize Hgcq $$ %Hcq
    iapply wp_stepLeader_checkQuorum c wp_ProgressTracker_QuorumActive wp_ProgressTracker_Visit
      wp_raft_becomeFollower wp_GetType r id s ml m ents ctx sn rs _ _ _ Hcq (G s.outbox) (G' s.outbox)
      $$ [Hphys Hm HG Hgcq]
    · iframe
      iexact Hinit
    inext
    iintro %err %s' ⟨Hphys, %Herr, %Hres, HR⟩
    iapply HΦ' $$ %err %s'
    iframe Hphys
    isplitr [HR]
    · ipureintro; exact Herr
    isplitr [HR]
    · ipureintro; exact Hres
    icases HR with (⟨%Hs, HG⟩ | ⟨%Hs, HG⟩)
    · subst Hs
      iright; iright
      iframe HG
      ipureintro
      refine ⟨?_, fun h => absurd (Hcq.symm.trans h.1) (by simp [MsgCheckQuorum, MsgAppResp])⟩
      rintro ⟨_, h⟩
      rw [Hlead] at h; exact absurd h (by decide)
    · obtain ⟨pvs, rfl⟩ := Hs
      ileft
      isplitr [HG]
      · ipureintro; exact ⟨Hcq, rfl⟩
      iidx HG
  by_cases Har : m.Type' = MsgAppResp
  · -- (slice 9) `MsgAppResp`: its gates; `Gc b N` back when `maybeCommit` ran
    have Hty := Har
    ihave HΦ0 : iprop(▷ ∀ (err : GoInterface) (s' : NState),
        ownRaftPhysCV c c.voters r id s' ∗
        ((∃ (b : Bool) (N : w64), ⌜m.Reject' = false ∧
            ∃ pvs : GMap w64 Progress, prvalsMatch pvs = appRespMatch s m.From' m.Index' ∧
              maybeCommitOut c { s with prvals := pvs } b N⌝ ∗ Gc b N s'.outbox) ∨
          (⌜¬ (m.Reject' = false ∧ AppRespRan s m.From' m.Index')⌝ ∗ G s'.outbox)) ∗
        ⌜err = interface.nil⌝ ∗
        ⌜LeaderNonpropResultC c id s m ents ctx s'⌝ -∗ Φ #err) $$ [HΦ']
    · inext
      iintro %err %s' ⟨Hphys, HR, %Herr, %Hres⟩
      iapply HΦ' $$ %err %s'
      iframe Hphys
      isplitr [HR]
      · ipureintro; exact Herr
      isplitr [HR]
      · ipureintro; exact Hres
      icases HR with (⟨%b, %N, %Hb, HGc⟩ | ⟨%Hn, HG⟩)
      · iright; ileft
        iexists b, N
        iframe HGc
        ipureintro; exact ⟨Hty, Hb⟩
      · iright; iright
        iframe HG
        ipureintro; exact ⟨fun h => Hcq h.1, fun h => Hn h.2⟩
    iapply wp_stepLeader_appresp c wp_raft_sendAppend wp_raft_maybeSendAppend
      wp_raft_bcastAppend wp_raft_maybeCommit wp_releasePendingReadIndexMessages
      wp_Progress_MaybeUpdate wp_Progress_MaybeDecrTo wp_Progress_BecomeProbe
      wp_Progress_BecomeReplicate wp_Progress_CanBumpCommit wp_Inflights_FreeLE
      wp_raftLog_findConflictByTerm wp_raftLog_lastIndex wp_raftLog_firstIndex
      wp_raft_sendTimeoutNow wp_GetType wp_GetFrom wp_GetReject wp_GetIndex wp_GetRejectHint
      wp_GetLogTerm r id s ml m Hty Hlead (Hfrom0 Hty) (fun Hr => Hself (Or.inr ⟨Hty, Hr⟩))
      (Hrdnz (Or.inr (Or.inl Hty))).2 (Hltr Hty) (Hrdnz (Or.inr (Or.inl Hty))).1.2.2 (Hack Hty).1 (fun h => (Hack h).2) ents ctx sn rs _ _ _
      G Gc HiG HiC $$ [Hphys Hm HG Hgsapp Hgcommit] HΦ0
    iframe Hphys Hm HG Hgcommit
    iframe Hinit Hgrlresp Hgrlhb Hgaapp Hgatnow Hnosnap
    iintro %Hrj
    iapply Hgsapp $$ %(Or.inr ⟨Hty, Hrj⟩)
  -- the other arms keep `G`
  ihave HΦG : iprop(▷ ∀ (err : GoInterface) (s' : NState),
      ownRaftPhysCV c c.voters r id s' ∗ G s'.outbox ∗ ⌜err = interface.nil⌝ ∗
      ⌜LeaderNonpropResultC c id s m ents ctx s'⌝ -∗ Φ #err) $$ [HΦ']
  · inext
    iintro %err %s' ⟨Hphys, HG, %Herr, %Hres⟩
    iapply HΦ' $$ %err %s'
    iframe Hphys
    isplitr [HG]
    · ipureintro; exact Herr
    isplitr [HG]
    · ipureintro; exact Hres
    iright; iright
    iframe HG
    ipureintro
    exact ⟨fun h => Hcq h.1, fun h => Har h.1⟩
  rcases Hty with Hty | Hty | Hty | Hty | Hty | Hty | Hty | Hty | Hty | Hty | Hty | Hty | Hty |
    Hty | Hty | Hty
  rotate_right 7
  ·
    -- an arm without a gate: `G` kept
    iapply wp_stepLeader_noop c wp_GetType wp_GetFrom r id s ml m ents ctx sn rs _ _ _
      (Or.inr (Or.inr (Or.inr (Or.inr Hty)))) G $$ [Hphys Hm HG] HΦG
    iframe
    iexact Hinit
  ·
    -- an arm without a gate: `G` kept
    iapply wp_stepLeader_rest0 c wp_GetType wp_GetFrom r id s ml m ents ctx sn rs _ _ _
      (Or.inl Hty) G $$ [Hphys Hm HG] HΦG
    iframe
    iexact Hinit
  ·
    -- an arm without a gate: `G` kept
    iapply wp_stepLeader_rest0 c wp_GetType wp_GetFrom r id s ml m ents ctx sn rs _ _ _
      (Or.inr Hty) G $$ [Hphys Hm HG] HΦG
    iframe
    iexact Hinit
  ·
    -- an arm without a gate: `G` kept
    iapply wp_stepLeader_report c wp_Progress_BecomeProbe wp_GetType wp_GetFrom wp_GetReject
      r id s ml m ents ctx sn rs _ _ _ (Or.inl Hty) G $$ [Hphys Hm HG] HΦG
    iframe
    iexact Hinit
  ·
    -- an arm without a gate: `G` kept
    iapply wp_stepLeader_report c wp_Progress_BecomeProbe wp_GetType wp_GetFrom wp_GetReject
      r id s ml m ents ctx sn rs _ _ _ (Or.inr Hty) G $$ [Hphys Hm HG] HΦG
    iframe
    iexact Hinit
  · ispecialize Hgtnow $$ %Hty
    ispecialize Hgxapp $$ %Hty
    iapply wp_stepLeader_transfer c wp_raft_sendAppend wp_raft_sendTimeoutNow
      wp_raftLog_lastIndex wp_raft_abortLeaderTransfer wp_GetType wp_GetFrom
      r id s ml m ents ctx sn rs _ _ _ Hty Hlead (Htz (Or.inr Hty)) (Hxtr Hty) G HiG
      $$ [Hphys Hm HG Hgtnow Hgxapp] HΦG
    iframe
    iframe Hinit Hnosnap
  · exact absurd Hty Hcq
  ·
    -- an arm without a gate: `G` kept
    iapply wp_stepLeader_noop c wp_GetType wp_GetFrom r id s ml m ents ctx sn rs _ _ _
      (Or.inl Hty) G $$ [Hphys Hm HG] HΦG
    iframe
    iexact Hinit
  · ihave #Hgb := Hgbeat $$ %Hty
    iapply wp_stepLeader_beat c wp_raft_bcastHeartbeat wp_GetType r id s ml m ents ctx sn rs
      _ _ _ Hty Hlead (Htz (Or.inl Hty)) G $$ [Hphys Hm HG] HΦG
    iframe
    iframe Hinit Hgb
  · obtain ⟨Hclen, Hcb, Hvne⟩ := Hhr Hty
    -- (slice 9) the flow-control append's and the read-index responses' gates
    ispecialize Hgsapp $$ %(Or.inl Hty)
    ihave #Hgr := Hghresp $$ %Hty
    iapply wp_stepLeader_hbresp c wp_raft_sendAppend wp_raftLog_lastIndex wp_readOnly_recvAck
      wp_readOnly_maybeAdvance wp_raft_responseToReadIndexReq wp_raft_send wp_GetType wp_GetFrom
      wp_GetContext wp_GetTo r id s ml m ents ctx sn rs _ _ _ Hty Hlead
      (Hrdnz (Or.inl Hty)).2
      (Hself (Or.inl Hty)) Hvne (Hrdnz (Or.inl Hty)).1 Hclen Hcb G HiG $$ [Hphys Hm HG Hgsapp] HΦG
    iframe
    iframe Hinit Hgr Hnosnap
  · exact absurd Hty Har
  · exact absurd Hty Hp
  ·
    -- an arm without a gate: `G` kept
    iapply wp_stepLeader_noop c wp_GetType wp_GetFrom r id s ml m ents ctx sn rs _ _ _
      (Or.inr (Or.inl Hty)) G $$ [Hphys Hm HG] HΦG
    iframe
    iexact Hinit
  ·
    -- an arm without a gate: `G` kept
    iapply wp_stepLeader_noop c wp_GetType wp_GetFrom r id s ml m ents ctx sn rs _ _ _
      (Or.inr (Or.inr (Or.inl Hty))) G $$ [Hphys Hm HG] HΦG
    iframe
    iexact Hinit
  ·
    -- an arm without a gate: `G` kept
    iapply wp_stepLeader_noop c wp_GetType wp_GetFrom r id s ml m ents ctx sn rs _ _ _
      (Or.inr (Or.inr (Or.inr (Or.inl Hty)))) G $$ [Hphys Hm HG] HΦG
    iframe
    iexact Hinit
  · ispecialize Hgriresp $$ %Hty
    ihave #Hgr := Hgrihb $$ %Hty
    iapply wp_stepLeader_readindex c
      wp_raft_committedEntryInCurrentTerm wp_sendMsgReadIndexResponse wp_GetType
      r id s ml m ents ctx sn rs _ _ _ Hty Hlead
      (Hrdnz (Or.inr (Or.inr Hty))).2 (Hri Hty) G $$ [Hphys Hm HG Hgriresp] HΦG
    iframe
    iframe Hinit Hgr

end proof

end EtcdGrove
end Perennial
