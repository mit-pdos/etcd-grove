/- Lean-first (no Rocq counterpart).

raft v3.7 (2026-10-16, stage R5): the message is a fresh `&pb.Message{Type: MsgHup.Enum()}`,
built as `msgIn` (`msgOwn_lit0`, `msgOwn_to_msgIn`) and given to `Step` for good. -/
module

public import RaftWitness.Spec.go_etcd_io.raft.v3.RawNode__Campaign
public import RaftWitness.Spec.go_etcd_io.raft.v3.raft__Step
public import RaftWitness.Spec.go_etcd_io.raft.v3.raftpb.MessageType__Enum
public import RaftWitness.Proof.go_etcd_io.raft.v3.LemmasRawnodeR
-- `Step.commit_mono`
public import RaftWitness.Proof.go_etcd_io.raft.v3.Protocol.Facts

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3
open RawNodeOwnAccess

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- A premise of `Step` about another message type: `MsgHup` (`W32 0`) is not it. -/
local macro "msg_ne" : tactic => `(tactic| (intro Hc; simp [MsgHup, MsgVote, MsgVoteResp,
  MsgPreVote, MsgPreVoteResp, MsgApp, MsgHeartbeat, MsgAppResp, MsgHeartbeatResp,MsgCheckQuorum, MsgSnap,
  MsgBeat, MsgProp, MsgStorageAppendResp, MsgStorageApplyResp, MsgReadIndex,
  MsgReadIndexResp, MsgForgetLeader, MsgUnreachable, MsgSnapStatus, MsgTimeoutNow, MsgTransferLeader] at Hc))

/-- `Step` on the literal message `pb.Message{Type: MsgHup}`; its `NetFrame` and
`TermStep` keep `ownRawNode` but for the term (`stepsOk_mono_le`). -/
theorem RawNode.Campaign.wp_proof
    (wp_raft_Step : raft.Step.spec (GF := GF) (hG := hG))
    (wp_MessageType_Enum : raftpb.MessageType.Enum.spec (GF := GF) (hG := hG)) :
    RawNode.Campaign.spec (GF := GF) (hG := hG) := by
  intro γ rn id rs Hterm Hflw
  wp_start as H
  iNamed H
  iNamed Hrn
  have Htc1 : uint.Z s.term + 1 ≤ uint.Z s.gh.tc := by rw [← Htrm, ← Hpvoff.2.1]; exact Hterm
  have Hnw : uint.Z s.term + 1 < 2 ^ 64 := by have : uint.Z s.gh.tc < 2 ^ 64 := by word
                                              omega
  wp_auto_lc 1
  rw [show raftpb.MsgHup = #((W32 0 : raftpb.MessageType)) from rfl]
  haveI : go.NotInterface go.int32 := ⟨by unfold go.int32; trivial⟩
  wp_apply wp_MessageType_Enum (W32 0) as %pty Hpty
  imod cellRO_alloc $$ Hpty with #cTy
  imod msgOwn_lit0 «$a0_ptr» _ ({ (zero_val MessageM) with Type' := W32 0 } : MessageM) ⊤ $$ [«$a0»] with Hm
  · iframe «$a0» cTy
    isplitr
    · ipureintro; simp
    msg_nulls
  ihave Hm := msgOwn_to_msgIn _ _ (by simp [MsgApp]) $$ Hm
  imod rdCred_zero_upd (GF := GF) γ with Hcr
  icases ownRaftPhysC_preFacts cf rnv.raft' id s (Hpvoff.dyn ⟨rs.capplied, rs.cfg, fp⟩) $$ Hphys with ⟨%Hpf, Hphys⟩
  have hP : (W32 0 : w32) ≠ MsgProp := by simp [MsgProp]
  wp_apply wp_raft_Step cf _ γ _ id s «$a0_ptr» ({ (zero_val MessageM) with Type' := W32 0 } : MessageM)
    [] [] none []
    (by simp [StepMsg, stepMsgTypes, MsgHup])
    (fun _ => ⟨rfl, Hnw, fun _ => Htc1, Hrnfl.1 Hflw⟩)
    (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne)
    (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne)
    (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne)
    (RestMsgOk.of_ne ⟨by msg_ne, by msg_ne, by msg_ne, by msg_ne, by msg_ne⟩) Hwf
    (GMode.Pre.of_facts Hpf (by msg_ne) (by msg_ne)) (fun h => absurd h (by msg_ne))
    $$ [$Hphys $Hghost $Hlc1 Hcr Hm]
  · -- the message: no entries, no `Context`, no snapshot
    simp only [hP, ↓reduceIte, named]
    isplitl [Hm]
    · iframe Hm
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
  simp only [hP]
  iintro %err %s' %c' %md' ⟨Hphys, Hghost, %Hwf', %Href, %Hcc, -, %Hfr, %Htm, -, Herr⟩
  have Hc := Href.commit_mono
  have e1 := Href.keep (by msg_ne) (by msg_ne); subst e1
  have e2 := Hcc (by msg_ne); subst c'
  wp_auto
  obtain ⟨Ha, Hsn, Hu, Hpv, Hsd, Hsg, Hpre, Hgh, Hfl', Hap'⟩ := Hfr (by msg_ne) (by msg_ne)
  obtain ⟨Ht1, Ht2, -, -, -, Hpcs⟩ := Htm (by msg_ne)
  have Ht2' := Ht2 rfl
  ihave #Hstr' := storedRecs_eq γ _ s'.logst.prev _ s'.logst.stored Hpv Hsd $$ Hstrecs
  icases Herr with (%Herr | ⟨%Hc', -⟩)
  · iapply HΦ $$ %err %s'.term
    simp only [named]
    isplitl [Hrn Hphys Hghost Hsteps Hsteps_cap Hpend]
    · iapply ownRawNode_intro γ rn id { rs with term := s'.term } s' cf fp rnv sv hprev steps Hwf' Hin Hal
        Hasync (by rw [Ha]; exact Hdlen) (by rw [Hu]; exact Hunp) (by rw [Hsn]; exact Hsnap)
        (stepsOk_mono_le s s' _ Ht1 ⟨Hpv, Hsd⟩ Hc Ha (tc_le_of_gh Hgh) Hstok) rfl (by rw [Hsg]; exact Hstor) 
        (Hpvoff.step rfl rfl Hpre Hgh (by have := Ht2 rfl; omega) Hpcs (fun _ => Htc1))
        (by rw [Hgh]; exact Hrs_out) (by rw [Hgh]; exact Hrs_unst) (Int.le_trans Hrs_clb Hc)
        (RNFl.keep Hrnfl Hfl' Hap' Ha)
        $$ Hrn Hphys Hghost Hsdrf Hsoft Hhard Hsteps Hsteps_cap Hpend Hdeliv Hstr'
    ipureintro
    rw [Htrm]
    exact ⟨⟨Ht1, Ht2'⟩, Herr⟩
  · exfalso; revert Hc'; msg_ne

end proof

end EtcdGrove
end Perennial
