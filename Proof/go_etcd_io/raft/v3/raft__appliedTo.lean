/-
Port of election_proof/proof_raft__appliedTo.v (857d09190).

Lean notes: Rocq's `wp_max2_uint64` is stepped by hand (`wp_func_call`, `wp_call`,
`wp_if_destruct`, as in `Proof/raftLog__appliedTo.lean`); each branch calls
`raftLog.appliedTo` at the value it computed, and the state is matched to `logAppliedTo`
(`w64Max`) with `ownRaftPhysC_eq`.

(2026-10-29, stage U5) The automatic leave: a leader at a configuration it leaves automatically
steps the proposal `confChangeToMsg(nil)` builds through `Step`'s `MsgProp` branch
(`StepProof.wp_Step_MsgProp`, imported from `Proof/raft__Step/`: the one proof module outside
`Step`'s own that takes a branch lemma, since the recursion `appliedTo` → `Step` cannot take
`Step`'s spec), over the specs of the functions that branch calls.
-/
module

public import Spec.go_etcd_io.raft.v3.raft__appliedTo
public import Spec.go_etcd_io.raft.v3.raftLog__appliedTo
public import Spec.go_etcd_io.raft.v3.confChangeToMsg
public import Proof.go_etcd_io.raft.v3.raft__Step.MsgProp
public import Spec.google_golang_org.protobuf.proto.UnmarshalConfChangeV2Empty

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

theorem raft.appliedTo.wp_proof
    (wp_raftLog_appliedTo : raftLog.appliedTo.spec (GF := GF) (hG := hG))
    -- (2026-10-29, stage U5) the automatic leave: `confChangeToMsg`, and the functions `Step`'s
    -- `MsgProp` branch calls (`wp_Step_MsgProp`)
    (wp_confChangeToMsg : confChangeToMsg.spec (GF := GF) (hG := hG))
    (wp_traceReceiveMessage : traceReceiveMessage.spec (GF := GF) (hG := hG))
    (wp_stepFollower : stepFollower.spec (GF := GF) (hG := hG))
    (wp_stepCandidate : stepCandidate.spec (GF := GF) (hG := hG))
    (wp_stepLeader : stepLeader.spec (GF := GF) (hG := hG))
    (wp_Message_GetType : raftpb.Message.GetType.spec (GF := GF) (hG := hG))
    (wp_Message_GetTerm : raftpb.Message.GetTerm.spec (GF := GF) (hG := hG))
    (wp_Message_GetFrom : raftpb.Message.GetFrom.spec (GF := GF) (hG := hG))
    (wp_Message_GetTo : raftpb.Message.GetTo.spec (GF := GF) (hG := hG))
    (wp_Message_GetIndex : raftpb.Message.GetIndex.spec (GF := GF) (hG := hG))
    (wp_Message_GetLogTerm : raftpb.Message.GetLogTerm.spec (GF := GF) (hG := hG))
    (wp_Message_GetCommit : raftpb.Message.GetCommit.spec (GF := GF) (hG := hG))
    (wp_Message_GetReject : raftpb.Message.GetReject.spec (GF := GF) (hG := hG))
    (wp_Message_GetEntries : raftpb.Message.GetEntries.spec (GF := GF) (hG := hG))
    (wp_Message_GetSnapshot : raftpb.Message.GetSnapshot.spec (GF := GF) (hG := hG))
    (wp_Message_GetContext : raftpb.Message.GetContext.spec (GF := GF) (hG := hG))
    (wp_Entry_GetIndex : raftpb.Entry.GetIndex.spec (GF := GF) (hG := hG))
    (wp_MessageType_Enum : raftpb.MessageType.Enum.spec (GF := GF) (hG := hG)) :
    raft.appliedTo.spec (GF := GF) (hG := hG) := by
  have Q : raft.Step.ReplPbPostulates (GF := GF) (hG := hG) :=
    ⟨wp_Message_GetType, wp_Message_GetTerm, wp_Message_GetFrom, wp_Message_GetTo,
     wp_Message_GetIndex, wp_Message_GetLogTerm, wp_Message_GetCommit, wp_Message_GetReject,
     wp_Message_GetEntries, wp_Message_GetSnapshot, wp_Message_GetContext, wp_Entry_GetIndex,
     wp_MessageType_Enum⟩
  intro c r id s index size k0 Hidx Hipo Hwf Hlnz HL Hsa Hapsb Hsx Hsp Hkx
  wp_start as H
  iNamed H
  wp_auto
  -- `oldApplied := r.raftLog.applied` (D22 S-d2: the struct in the windows)
  wp_apply raft.wp_load_raftLogCW $$ Hphys as Hphys
  icases ownRaftPhysCVW_log_at c r id s $$ Hphys with ⟨Hlog, %Hgh0, Hback⟩
  icases ownRaftLogW_struct _ _ $$ Hlog with ⟨%lv, Hl, %Hlv, Hlb⟩
  obtain ⟨Hap, Hapl, Hapc, -, -⟩ := Hlv
  wp_auto
  ihave Hlog := Hlb $$ Hl
  ihave Hphys := Hback $$ %s.logst Hlog %Hgh0 %(fun _ => Int.le_refl _)
  ihave Hphys := ownRaftPhysCVW_eq c r id _ s (by cases s; rfl) $$ Hphys
  rw [Hap]
  generalize Hs1 : ({ s with logst := logAppliedTo s.logst index size } : NState) = s1
  have Hs1role : s1.role = s.role := by rw [← Hs1]
  have Hs1term : s1.term = s.term := by rw [← Hs1]
  have Hs1ps : toPState s1 = toPState s := by rw [← Hs1]; rfl
  have Hwf1 : s.role = .leader → NStateWf s1 := fun h => by rw [← Hs1]; exact Hwf h
  -- `max(index, oldApplied)`, as `w64Max`
  wp_func_call
  wp_call
  wp_if_destruct
  all_goals
    -- `r.raftLog.appliedTo(newApplied, size)`: the window ends, the struct is quiet again
    wp_apply raft.wp_load_raftLogCW $$ Hphys as Hphys
    icases ownRaftPhysCVW_log_atQ c r id s $$ Hphys with ⟨Hlog, %Hgh0, Hback⟩
    first
      | wp_apply wp_raftLog_appliedTo _ _ index size (by omega) Hipo Hsx Hsp $$ [$Hlog] as Hlog
      | wp_apply wp_raftLog_appliedTo _ _ s.logst.applied size (by omega)
          (fun h => absurd Hapl (Int.not_le.2 h)) (fun _ _ h => absurd Hapl (Int.not_le.2 h))
          (fun _ _ h => absurd Hapl (Int.not_le.2 h))
          $$ [$Hlog] as Hlog
    ihave Hlog := ownRaftLogW_quietW _ _ $$ Hlog %(⟨Hsa, by
      cases h : s.logst.aps
      · rfl
      · have := Hapsb h
        simp only [Bool.true_and, decide_eq_false_iff_not]
        omega⟩)
    ihave Hphys := Hback $$ %_ Hlog %(LogGhOk.of_fields Hgh0 rfl rfl rfl rfl rfl
        (hx := fun h => SnpExt.raise h rfl rfl rfl (by simp only; rw [w64Max_spec]; omega)
          (fun ha k hk => by
            have := Hkx ha k hk
            simp only; rw [w64Max_spec]
            first | omega | (simp only [decide_eq_true_eq, decide_eq_false_iff_not] at *; omega))))
      %(fun _ => logLast_le_of_fields rfl rfl rfl)
    -- the state at the new `applied`, `s1`
    ihave Hphys := ownRaftPhysC_eq c _ _ _ s1 (by
        rw [← Hs1]; simp only [logAppliedTo, w64Max]
        split <;> first | rfl | omega) $$ Hphys
    -- `r.trk.Config.AutoLeave`
    icases ownRaftPhysC_tracker_same c r id _ $$ Hphys with ⟨%tv, Htrkf, Htrk, Htback⟩
    icases ownTrackerC_autoleave c _ _ $$ Htrk with ⟨%Hal, Htrk⟩
    wp_auto
    rw [Hal]
    ihave Hphys := Htback $$ %tv Htrkf Htrk
    -- nothing more: `LeaveStep`'s first case
    have Hnone : LeaveStep c id s1 s1 (plogLastIndexZ (toPState s).base (toPState s).log) [] :=
      .inl ⟨rfl, rfl, by rw [Hs1ps]⟩
    cases Hcal : c.autoLeave
    · wp_auto
      iapply HΦ $$ %s1 %(plogLastIndexZ (toPState s).base (toPState s).log) %([] : List Msg)
      iframe Hphys
      isplitr
      · ipureintro; exact Hnone
      · iintro %Hlt; exact absurd Hlt (Int.lt_irrefl _)
    · wp_auto
      wp_apply raft.wp_load_pendingConfIndexC $$ Hphys as Hphys
      wp_if_destruct
      · wp_apply raft.wp_load_stateC $$ Hphys as Hphys
        try wp_auto
        by_cases Hrl : s1.role = .leader
        · -- a leader at a configuration it leaves automatically: propose the leave
          rw [decide_eq_true (show stateW64 s1.role = W64 2 by rw [Hrl]; rfl)]
          try wp_auto
          icases ownRaftPhysC_last_bound c r id s1 $$ Hphys with ⟨%HL1, Hphys⟩
          wp_apply wp_confChangeToMsg interface.nil none DFrac.discard $$ []
            as %ml %bs ⟨-, Hm, %Hbs⟩
          · unfold ownConfChangeI; ipureintro; rfl
          simp only [MarshalsConfChange] at Hbs
          subst Hbs
          try wp_auto
          ihave #Hcc := ccEntsOk_leave (GF := GF)
          wp_apply (StepProof.wp_Step_MsgProp wp_traceReceiveMessage wp_stepFollower
              wp_stepCandidate wp_stepLeader Q c r id s1 ml leaveMsgM none [] [] [leaveEntM]
              [some (.v2 ConfChangeV2M.empty)] k0 rfl rfl (.inl rfl) (by simp) (by simp)
              (fun h => absurd (h.symm.trans Hrl) (by decide))
              (fun _ => by rw [Hs1term]; exact Hlnz (Hs1role ▸ Hrl)) (Hwf1 (Hs1role ▸ Hrl))
              (by rw [Hs1ps]; exact HL (Hs1role ▸ Hrl)) rfl)
            $$ [$Hphys Hm $Hcc $Hrc]
            as %err %s' %B ⟨Hphys, %HBb, Hrcb, %Hwf', %Hfr, %Happl, %Hpk, %Hst, Herr⟩
          · rw [show leaveMsgM = propMsgM from rfl, show leaveEntM = ccEntryM none [] from rfl]
            iexact Hm
          obtain ⟨recv, Hrecv, Hrl1, Hstep⟩ := Hst
          have Hout : LeaveStep c id s1 s' B recv :=
            .inr ⟨Hcal, Hrl, Hrecv, Hrl1, Hstep, Hfr.1, Hfr.2, Happl, Hwf', HBb.1, by
              have := HBb.2.1; simpa using this, HBb.2.2, HL1⟩
          -- the log line, either way
          cases err
          all_goals
            try wp_auto
            icases ownRaftPhysC_tracker_same c r id _ $$ Hphys with ⟨%tv2, Htrkf, Htrk, Htback⟩
            wp_auto
            ihave Hphys := Htback $$ %tv2 Htrkf Htrk
            try wp_raft_logC
            try wp_auto
            iapply HΦ $$ %s' %B %recv
            iframe Hphys
            isplitr
            · ipureintro; exact Hout
            · iintro %Hlt
              rw [← Hs1ps] at Hlt
              iapply Hrcb $$ %Hlt
        · have Hst : stateW64 s1.role ≠ W64 2 := by
            cases h : s1.role <;> simp_all [stateW64] <;> decide
          rw [decide_eq_false (show ¬ (stateW64 s1.role = W64 2) from Hst)]
          try wp_auto
          iapply HΦ $$ %s1 %(plogLastIndexZ (toPState s).base (toPState s).log) %([] : List Msg)
          iframe Hphys
          isplitr
          · ipureintro; exact Hnone
          · iintro %Hlt; exact absurd Hlt (Int.lt_irrefl _)
      · try wp_auto
        iapply HΦ $$ %s1 %(plogLastIndexZ (toPState s).base (toPState s).log) %([] : List Msg)
        iframe Hphys
        isplitr
        · ipureintro; exact Hnone
        · iintro %Hlt; exact absurd Hlt (Int.lt_irrefl _)

end proof

end EtcdGrove
end Perennial
