/- Proof of `Spec/go_etcd_io/raft/v3/RawNode__ProposeConfChange.lean`, Lean-first
(2026-10-13). As `RawNode.Propose`'s, on `confChangeToMsg`'s message; the entry's data is
recorded as proposed (`propRegister`), which gives its `entData` (`entData_cc`) and the
bytes `Step` needs (`ccEntsOk_cc`). 
raft v3.7 (2026-10-16, stage R5): `confChangeToMsg` returns the message `msgIn ml 1`, which is
passed to `Step` for good; the entry's bytes are in its record (D6), so no registration of the
data (`propRegister`) and `entData_cc`/`ccEntsOk_cc` are pure.
-/
module

public import RaftWitness.Spec.go_etcd_io.raft.v3.RawNode__ProposeConfChange
public import RaftWitness.Spec.go_etcd_io.raft.v3.confChangeToMsg
public import RaftWitness.Spec.go_etcd_io.raft.v3.raft__Step
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

/-- A premise of `Step` about another message type: `MsgProp` (`W32 2`) is not it. -/
local macro "msg_ne" : tactic => `(tactic| (intro Hc; simp [propMsgM, MsgProp, MsgHup, MsgVote,
  MsgVoteResp, MsgPreVote, MsgPreVoteResp, MsgApp, MsgHeartbeat, MsgAppResp, MsgHeartbeatResp,MsgCheckQuorum,
  MsgSnap, MsgBeat, MsgStorageAppendResp, MsgStorageApplyResp, MsgReadIndex, MsgReadIndexResp,
  MsgForgetLeader, MsgUnreachable, MsgSnapStatus, MsgTimeoutNow, MsgTransferLeader] at Hc))

theorem RawNode.ProposeConfChange.wp_proof
    (wp_confChangeToMsg : confChangeToMsg.spec (GF := GF) (hG := hG))
    (wp_raft_Step : raft.Step.spec (GF := GF) (hG := hG)) :
    RawNode.ProposeConfChange.spec (GF := GF) (hG := hG) := by
  intro γ rn id rs c o dq Hok
  wp_start as H
  iNamed H
  iNamed Hrn
  wp_auto_lc 1
  wp_apply wp_confChangeToMsg c (some o) dq $$ [$Hc] as %ml %bs ⟨Hc, Hm, %Hbs⟩
  ihave #Hent := entData_cc γ o bs Hbs (Hok bs Hbs)
  ihave #Hcc := ccEntsOk_cc (GF := GF) o bs Hbs
  imod rdCred_zero_upd (GF := GF) γ with Hcr
  icases ownRaftPhysC_preFacts cf rnv.raft' id s (Hpvoff.dyn ⟨rs.capplied, rs.cfg, fp⟩) $$ Hphys with ⟨%Hpf, Hphys⟩
  wp_apply wp_raft_Step cf _ γ _ id s ml propMsgM [ccEntryM (some o) bs] [] none []
    (by simp [StepMsg, stepMsgTypes, propMsgM, MsgProp]) 
    (by msg_ne) (by msg_ne)
    (by msg_ne) (by msg_ne)
    (by msg_ne) (by msg_ne)
    (by msg_ne) (by msg_ne)
    (by msg_ne) (by msg_ne)
    (by msg_ne)
    (fun _ => ⟨rfl, .inl rfl⟩) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne)
    (RestMsgOk.of_ne ⟨by msg_ne, by msg_ne, by msg_ne, by msg_ne, by msg_ne⟩) Hwf
    (GMode.Pre.of_facts Hpf (by msg_ne) (by msg_ne)) (fun h => absurd h (by msg_ne))
    $$ [$Hphys $Hghost $Hlc1 Hm Hcr]
  · -- the message: its one-entry batch, owned, with the entry's bytes; `Context` nil
    simp only [propMsgM, MsgProp, ite_true]
    isplitl [Hm]
    · simp only [named]
      isplitl [Hm]
      · iexact Hm
      isplitr
      · isplitr
        · iexists [some o]
          iexact Hcc
        iapply (BigSepL.bigSepL_singleton (Φ := fun _ e => entTk (GF := GF) γ e)).2
        iapply entTk_cc
      isplitr
      · ipureintro
        intro _
        exact ⟨List.cons_ne_nil _ _, by simp⟩
      isplitr
      · ipureintro
        intro Hc
        simp [MsgStorageApplyResp] at Hc
      · imodintro
        iintro %ty %Hty _
        rw [show mtypeOf (W32 2) = some .propose from rfl] at Hty
        cases Hty
        unfold isMessage absMsg absMsgFrom
        isplitr
        · ipureintro
          exact ⟨rfl, List.cons_ne_nil _ _, by simp⟩
        iapply (BigSepL.bigSepL_singleton (Φ := fun _ e => propData (GF := GF) γ e)).2
        iexact Hent
    isplitl [Hcr]
    · have H215 : ¬ ((W32 2 : w32) = W32 15) := by word
      simp only [MsgReadIndex, H215, ite_false]
      iexact Hcr
    · imodintro
      iintro %Hc
      simp [MsgSnap] at Hc
  simp only [propMsgM, MsgProp]
  iintro %err %s' %c' %md' ⟨Hphys, Hghost, %Hwf', %Href, %Hc', %Hloc, %_, %_, %_, Herr⟩
  have Hc := Href.commit_mono
  have e1 := Href.keep (by msg_ne) (by msg_ne); subst e1
  have e2 := Hc' (by msg_ne); subst c'
  wp_auto
  -- what the `RawNode` tracks is kept: `LocalStepOk`, and the commit index does not move
  -- back (`Step.commit_mono`)
  obtain ⟨Hfr, Hap, -⟩ := Hloc (.inl rfl)
  have Hap' := Hap (fun Hc => absurd Hc (by msg_ne))
  ihave #Hstr' := storedRecs_eq γ _ s'.logst.prev _ s'.logst.stored Hfr.2.2.2.2.1
    Hfr.2.2.2.2.2.1 $$ Hstrecs
  iapply HΦ
  simp only [named]
  iframe Hc
  isplitl [Hrn Hphys Hghost Hsteps Hsteps_cap Hpend]
  · iapply ownRawNode_intro γ rn id rs s' cf fp rnv sv hprev steps Hwf' Hin Hal Hasync
      (by rw [Hap']; exact Hdlen) (by rw [Hfr.2.2.1]; exact Hunp)
      (by rw [Hfr.2.2.2.1]; exact Hsnap)
      (stepsOk_mono s s' _ Hfr.1 ⟨Hfr.2.2.2.2.1, Hfr.2.2.2.2.2.1⟩ Hc Hap'
        (tc_le_of_gh Hfr.2.2.2.2.2.2.2.2.1) Hstok)
      (by rw [Hfr.1]; exact Htrm) (by rw [Hfr.2.2.2.2.2.2.1]; exact Hstor)
      (Hpvoff.keep rfl rfl Hfr.2.2.2.2.2.2.2.1 Hfr.2.2.2.2.2.2.2.2.1 Hfr.1 Hfr.2.2.2.2.2.2.2.2.2.1)
      (by rw [Hfr.2.2.2.2.2.2.2.2.1]; exact Hrs_out) (by rw [Hfr.2.2.2.2.2.2.2.2.1]; exact Hrs_unst)
      (Int.le_trans Hrs_clb Hc)
      (RNFl.keep Hrnfl Hfr.2.2.2.2.2.2.2.2.2.2.1 Hfr.2.2.2.2.2.2.2.2.2.2.2 Hap')
      $$ Hrn Hphys Hghost Hsdrf Hsoft Hhard Hsteps Hsteps_cap Hpend Hdeliv Hstr'
  icases Herr with (%Herr | ⟨-, #Hd⟩)
  · ileft; ipureintro; exact Herr
  · iright; iexact Hd

end proof

end EtcdGrove
end Perennial
