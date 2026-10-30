/- Lean-first (no Rocq counterpart), 2026-10-13. 
raft v3.7 (2026-10-16, stage R5): the message is a fresh `&pb.Message{Type: MsgTransferLeader.Enum(), ...}`,
its scalar fields fresh cells, built as `msgIn` (`msgOwn_lit0`, `msgOwn_to_msgIn`) and given to
`Step` for good. -/
module

public import Spec.go_etcd_io.raft.v3.RawNode__TransferLeader
public import Spec.go_etcd_io.raft.v3.raft__Step
public import Spec.go_etcd_io.raft.v3.raftpb.MessageType__Enum
public import Proof.go_etcd_io.raft.v3.LemmasRawnodeR
public import Proof.go_etcd_io.raft.v3.LemmasP3bXw
-- `Step.commit_mono`
public import Proof.go_etcd_io.raft.v3.Protocol.Facts

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3
open RawNodeOwnAccess

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- A premise of `Step` about another message type. -/
local macro "msg_ne" : tactic => `(tactic| (intro Hc; simp [MsgHup, MsgVote, MsgVoteResp,
  MsgPreVote, MsgPreVoteResp, MsgApp, MsgHeartbeat, MsgAppResp, MsgHeartbeatResp,MsgCheckQuorum, MsgSnap,
  MsgBeat, MsgProp, MsgStorageAppendResp, MsgStorageApplyResp, MsgReadIndex,
  MsgReadIndexResp, MsgForgetLeader, MsgUnreachable, MsgSnapStatus, MsgTimeoutNow,
  MsgTransferLeader] at Hc))

/-- `Step` on the literal message: a local message, the term unchanged. -/
theorem RawNode.TransferLeader.wp_proof
    (wp_raft_Step : raft.Step.spec (GF := GF) (hG := hG))
    (wp_MessageType_Enum : raftpb.MessageType.Enum.spec (GF := GF) (hG := hG)) :
    RawNode.TransferLeader.spec (GF := GF) (hG := hG) := by
  intro γ rn id rs transferee
  wp_start as H
  iNamed H
  iNamed Hrn
  wp_auto_lc 1
  rw [show raftpb.MsgTransferLeader = #((W32 13 : raftpb.MessageType)) from rfl]
  haveI : go.NotInterface go.int32 := ⟨by unfold go.int32; trivial⟩
  wp_apply wp_MessageType_Enum (W32 13) as %pty Hpty
  imod cellRO_alloc $$ Hpty with #cTy
  imod cellRO_alloc $$ «$v1» with #cFr
  imod msgOwn_lit0 «$a0_ptr» _ ({ (zero_val MessageM) with Type' := W32 13, From' := transferee } : MessageM) ⊤ $$ [«$a0»] with Hm
  · iframe «$a0» cTy cFr
    isplitr
    · ipureintro; simp
    msg_nulls
  ihave Hm := msgOwn_to_msgIn _ _ (by simp [MsgApp]) $$ Hm
  imod rdCred_zero_upd (GF := GF) γ with Hcr
  icases ownRaftPhysC_preFacts cf rnv.raft' id s (Hpvoff.guard rs.capplied rs.cfg (ds := ds)) $$ Hphys with ⟨%Hpf, Hphys⟩
  icases ownRaftPhysC_sn cf rnv.raft' id s $$ Hphys with ⟨%Hns0, Hphys⟩
  wp_apply wp_raft_Step cf _ γ _ id s «$a0_ptr» ({ (zero_val MessageM) with Type' := W32 13, From' := transferee } : MessageM) [] [] none []
    (by simp [StepMsg, stepMsgTypes, MsgTransferLeader]) 
    (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne)
    (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne)
    (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne)
    (⟨fun h => absurd h (by msg_ne), fun h => absurd h (by msg_ne), fun _ => ⟨rfl, rfl⟩⟩ : RestMsgOk s _ [] []) Hwf
    (GMode.Pre.of_facts Hpf (by msg_ne) (by msg_ne)) (fun h => absurd h (by msg_ne))
    $$ [$Hphys $Hghost $Hlc1 Hcr Hm]
  · -- the message: no entries, no `Context`, no snapshot
    have hP : (W32 13 : w32) ≠ MsgProp := by simp [MsgProp]
    simp only [hP, ↓reduceIte, named]
    -- (raft-final phase 2) unstamped: no transfer witness needed
    isplitr
    · imodintro
      iintro %h
      exact (h.2 rfl).elim
    isplitl [Hm]
    · iframe Hm
      repeat (isplitr; · first | iempintro | (ipureintro; simp) | (ipureintro; msg_ne))
      imodintro
      iintro %ty %Hty
      rw [show mtypeOf (W32 13) = none from rfl] at Hty
      cases Hty
    isplitl [Hcr]
    · rw [ite_eq_right (by msg_ne)]; iexact Hcr
    imodintro
    iintro %Hc
    simp [MsgSnap] at Hc
  have hP : (W32 13 : w32) ≠ MsgProp := by simp [MsgProp]
  simp only [hP]
  iintro %err %s' %c' %md' ⟨Hphys, Hghost, %Hwf', %Href, %Hcc, -, -, %Hxwf, %Htm, -, -, -, Herr⟩
  have Hc := Href.commit_mono
  have e1 := Href.keep (by msg_ne) (by msg_ne) (fun h => absurd h (by msg_ne)); subst e1
  have e2 := Hcc (by msg_ne); subst c'
  wp_auto
  -- (raft-final phase 2) the forward may record `(lead, term)` in `xw` (`"%Hxwframe"`): `NetFrame` at
  -- the ghost state before the step, which the step changes only in `xw`
  obtain ⟨⟨Ha, Hsn, Hu, Hpv, Hsd, Hsg, Hpre, -, Hfl', Hap'⟩, Hgx, -⟩ := Hxwf rfl
  simp only at Ha Hsn Hu Hpv Hsd Hsg Hpre Hfl' Hap'
  icases ownRaftPhysC_sn cf rnv.raft' id s' $$ Hphys with ⟨%Hsn1, Hphys⟩
  have Hsneq : s'.gh.sn = s.gh.sn := by rw [Hgx]
  have Htceq : s'.gh.tc = s.gh.tc := by rw [Hgx]
  obtain ⟨Ht1, -, Ht3, Hip4, -, Hpcs⟩ := Htm (by msg_ne)
  have Ht3 := Ht3 (by msg_ne) (by msg_ne) (by msg_ne)
  have H0 : uint.Z (zero_val MessageM).Term' = 0 := rfl
  simp only [H0] at Ht3
  have Htrm' : rs.term = s'.term := by
    rw [Htrm]
    have h0 : 0 ≤ uint.Z s.term := by word
    have h2 : uint.Z s'.term ≤ uint.Z s.term := by
      omega
    word
  ihave #Hstr' := ackInv_keep (rs' := rs) γ rfl Hstok Ht1 Hpv Hsn (logStoreRec_stored Hsd) (Hip4 (by msg_ne)) $$ Hstrecs
  icases Herr with (%Herr | ⟨%Hc', -⟩)
  · iapply HΦ
    simp only [named]
    
    ihave #Hsloc' := snapLocOk_keep γ id (.inl Hsn) $$ Hsloc
    iapply ownRawNode_intro γ rn id rs s' cf fp rnv sv hprev steps Hwf' Hin
      Hasync (by rw [Ha]; exact Hdlen) (by rw [Hu]; exact Hunp) (by rw [Hsn]; exact Hsnap)
      (stepsOk_mono_le s s' _ Ht1 ⟨Hpv, (logStoreRec_stored Hsd)⟩ Hc Ha (Int.le_of_eq (congrArg _ Htceq.symm)) Hstok) Htrm'
      (by rw [Hsg]; exact ⟨Hstor.1, by rw [Hsn1.2, Hsneq, ← Hns0.2]; exact Hstor.2⟩)
      (Hpvoff.step_gxw rfl rfl Hpre Hgx (by rw [← Htrm', Htrm]; exact Hpvoff.2.2.1) Hpcs
          (by msg_ne))
      (by rw [Hgx]; exact Hrs_out) (by rw [Hgx]; exact Hrs_unst) (Int.le_trans Hrs_clb Hc)
        (RNFl.keep Hrnfl Hfl' Hap' Ha) (by
          have H := Hloan.step_gxw (b := false) rs.term Hgx
            (fun _ => ⟨.inl Hsn, Hfl', logStoreRec_stored Hsd, Hu, Ha, Hc⟩)
          simp only [Bool.or_false] at H
          exact H)
      (Hsdt.ofRec Hsn Hsd) $$ Hrn Hphys Hghost Hsdrf Hsoft Hhard Hsteps Hsteps_cap Hpend Hdeliv Hstr' Hloanc Hsloc'
    
  · exfalso; revert Hc'; msg_ne

end proof

end EtcdGrove
end Perennial
