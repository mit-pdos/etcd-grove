/- Port of election_proof/proof_RawNode__Propose.v.

Lean notes: like its spec, the section fixes `hlc := HasLC.hasLC` and has `[AllG GF]`.
-/
module

public import Spec.go_etcd_io.raft.v3.RawNode__Propose
public import Spec.go_etcd_io.raft.v3.raft__Step
-- `Step.commit_mono`
public import Proof.go_etcd_io.raft.v3.Protocol.Facts

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
local macro "msg_ne" : tactic => `(tactic| (intro Hc; simp [MsgHup, MsgVote, MsgVoteResp,
  MsgPreVote, MsgPreVoteResp, MsgApp, MsgHeartbeat, MsgAppResp, MsgHeartbeatResp, MsgSnap,
  MsgBeat, MsgStorageAppendResp, MsgStorageApplyResp, MsgReadIndex, MsgReadIndexResp, MsgForgetLeader, MsgUnreachable, MsgSnapStatus, MsgTimeoutNow, MsgTransferLeader] at Hc))

/-- `Step` on the literal message: `Type: MsgProp`, `From: r.id`, the one-entry batch;
every other field zero. Its `MsgProp` arm, at the singleton batch, is the
postcondition; `LocalStepOk` and `Step.commit_mono` keep `ownRawNode` at `rs`. -/
theorem RawNode.Propose.wp_proof
    (wp_raft_Step : raft.Step.spec (GF := GF) (hG := hG)) :
    RawNode.Propose.spec (GF := GF) (hG := hG) := by
  intro γ rn id rs data_sl data
  wp_start as H
  iNamed H
  iNamed Hrn
  wp_auto
  wp_apply raft.wp_load_idC $$ Hphys as Hphys
  icases ownRaftPhysC_preFacts cf rnv.raft' id s Hpvoff $$ Hphys with ⟨%Hpf, Hphys⟩
  wp_apply wp_slice_literal (l := [propEntry data_sl])
  isplitr
  · ipureintro; rfl
  iintro %sl_ptr ⟨Hes, Hcap⟩
  wp_auto
  imod rdCred_zero_upd (GF := GF) γ with Hcr
  wp_apply wp_raft_Step cf _ γ _ id s _ [propEntry data_sl] []
    (by simp [StepMsg, stepMsgTypes, MsgProp]) 
    (by msg_ne) (by msg_ne)
    (by msg_ne) (by msg_ne)
    (by msg_ne) (by msg_ne)
    (by msg_ne) (by msg_ne)
    (by msg_ne) (by msg_ne)
    (by msg_ne)
    (fun _ => ⟨rfl, .inr rfl⟩) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne)
    (RestMsgOk.of_ne ⟨by msg_ne, by msg_ne, by msg_ne, by msg_ne, by msg_ne⟩) Hwf
    (GMode.Pre.of_facts Hpf (by msg_ne) (by msg_ne))
    $$ [$Hphys $Hghost Hes Hcap Hcr]
  · -- the message: its one-entry batch, owned; `Context` nil
    simp only [MsgProp, ite_true]
    isplitl [Hes Hcap]
    · simp only [named]
      isplitl [Hes]
      · iframe Hes
        iexists ([propEntry data_sl].map fun _ => none)
        iapply ccEntsOk_normal [propEntry data_sl]
        intro e He
        simp only [List.mem_singleton] at He
        subst He
        rfl
      isplitl [Hcap]
      · iexact Hcap
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
        iapply (BigSepL.bigSepL_singleton (Φ := fun _ e => entData (GF := GF) γ e)).2
        iexact Hent
    isplitr
    · iapply ownSlice_nil
    isplitl [Hcr]
    · rw [if_neg (by msg_ne)]; iexact Hcr
    · imodintro
      iintro %Hc
      simp [MsgSnap] at Hc
  simp only [MsgProp, ite_true]
  iintro %err %s' %c' %md' ⟨Hphys, Hghost, %Hwf', %Href, %Hc', %Hloc, %_, %_, %_, Herr⟩
  have Hc := Href.commit_mono
  have e1 := Href.keep (by msg_ne) (by msg_ne); subst e1
  have e2 := Hc' (by msg_ne); subst c'
  wp_auto
  -- what the `RawNode` tracks is kept: `LocalStepOk`, and the commit index does not move
  -- back (`Step.commit_mono`)
  obtain ⟨Hfr, Hap⟩ := Hloc (.inl rfl)
  have Hap' := Hap (fun Hc => absurd Hc (by msg_ne))
  ihave #Hstr' := storedRecs_eq γ _ s'.logst.prev _ s'.logst.stored Hfr.2.2.2.2.1
    Hfr.2.2.2.2.2.1 $$ Hstrecs
  iapply HΦ
  simp only [named]
  isplitl [Hrn Hphys Hghost Hsteps Hsteps_cap Hpown]
  · iapply ownRawNode_intro γ rn id rs s' cf fp rnv sv steps Hwf' Hin Hal Hasync
      (by rw [Hap']; exact Hdlen) (by rw [Hfr.2.2.1]; exact Hunp)
      (by rw [Hfr.2.2.2.1]; exact Hsnap)
      (stepsOk_mono s s' _ Hfr.1 ⟨Hfr.2.2.2.2.1, Hfr.2.2.2.2.2.1⟩ Hc Hap'
        Hfr.2.2.2.2.2.2.2.1 Hstok)
      (by rw [Hfr.1]; exact Htrm) (by rw [Hfr.2.2.2.2.2.2.1]; exact Hstor)
      (by rw [Hfr.2.2.2.2.2.2.2.1]; exact Hpvoff)
      (by rw [Hfr.2.2.2.2.2.2.2.2]; exact Hrs_out) (by rw [Hfr.2.2.2.2.2.2.2.2]; exact Hrs_unst)
      (Int.le_trans Hrs_clb Hc)
      $$ Hrn Hphys Hghost Hsdrf Hsoft Hsteps Hsteps_cap Hpend Hpown Hdeliv Hstr'
  icases Herr with (%Herr | ⟨-, #Hd⟩)
  · ileft; ipureintro; exact Herr
  · iright; iexact Hd

end proof

end EtcdGrove
end Perennial
