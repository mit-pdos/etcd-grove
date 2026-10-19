/- Port of election_proof/proof_RawNode__Propose.v.

Lean notes: like its spec, the section fixes `hlc := HasLC.hasLC` and has `[AllG GF]`.

raft v3.7 (2026-10-16, stage R5): the message is a fresh `&pb.Message{Type: MsgProp.Enum(), From:
new(r.id), Entries: []*pb.Entry{{Data: data}}}`: the entry allocated by the slice literal
(`wp_slice_literal_ex`), holding the caller's frozen bytes (D6), frozen (`entOwn_freeze`); the
message `msgIn` with its entries' slots owned (`Step`'s for a `MsgProp`).
-/
module

public import Spec.go_etcd_io.raft.v3.RawNode__Propose
public import Spec.go_etcd_io.raft.v3.raft__Step
public import Spec.go_etcd_io.raft.v3.raftpb.MessageType__Enum
public import Proof.go_etcd_io.raft.v3.LemmasRawnodeR
public import Proof.go_etcd_io.raft.v3.LemmasMemstorage
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
  MsgPreVote, MsgPreVoteResp, MsgApp, MsgHeartbeat, MsgAppResp, MsgHeartbeatResp,MsgCheckQuorum, MsgSnap,
  MsgBeat, MsgStorageAppendResp, MsgStorageApplyResp, MsgReadIndex, MsgReadIndexResp, MsgForgetLeader, MsgUnreachable, MsgSnapStatus, MsgTimeoutNow, MsgTransferLeader] at Hc))

/-- `Step` on the literal message: `Type: MsgProp`, `From: r.id`, the one-entry batch;
every other field zero. Its `MsgProp` arm, at the singleton batch, is the
postcondition; `LocalStepOk` and `Step.commit_mono` keep `ownRawNode` at `rs`. -/
theorem RawNode.Propose.wp_proof
    (wp_raft_Step : raft.Step.spec (GF := GF) (hG := hG))
    (wp_MessageType_Enum : raftpb.MessageType.Enum.spec (GF := GF) (hG := hG)) :
    RawNode.Propose.spec (GF := GF) (hG := hG) := by
  intro γ rn id rs data_sl data
  wp_start as H
  iNamed H
  iNamed Hrn
  wp_auto_lc 1
  rw [show raftpb.MsgProp = #((W32 2 : raftpb.MessageType)) from rfl]
  haveI : go.NotInterface go.int32 := ⟨by unfold go.int32; trivial⟩
  wp_apply wp_MessageType_Enum (W32 2) as %pty Hpty
  imod cellRO_alloc $$ Hpty with #cTy
  wp_apply raft.wp_load_idC $$ Hphys as Hphys
  icases ownRaftPhysC_preFacts cf rnv.raft' id s (Hpvoff.dyn ⟨rs.capplied, rs.cfg, fp⟩) $$ Hphys with ⟨%Hpf, Hphys⟩
  wp_apply wp_slice_literal_ex (V := Loc)
  wp_alloc l0 as Hl0
  wp_auto
  iexists [l0]
  isplitr
  · ipureintro; rfl
  iintro %slp ⟨Hsl, Hsl_cap⟩
  have Hsz : go.arrayLiteralSize [KeyedElement none (ElementLiteralValue
      [KeyedElement (some (KeyField go!"Data")) (ElementExpression go.byte.SliceType #data_sl)])] = 1 := rfl
  simp only [Hsz]
  imod entOwn_of_struct l0 (⟨zero_val _, null, null, null, data_sl, slice.nil, 0⟩ : raftpb.Entry)
      (propEntryM data) ⊤ rfl $$ [Hl0] with He
  · iframe Hl0
    simp only [propEntryM]
    iframe Hdata
    repeat (isplitr; · iunfold cellRO; ileft; ipureintro; exact ⟨rfl, rfl⟩)
    iunfold cellRO; ileft; ipureintro; exact ⟨rfl, rfl⟩
  imod entOwn_freeze $$ He with #He
  wp_auto
  imod cellRO_alloc $$ «$v1» with #cFr
  ihave #Hnilb := ownSlice_nil (V := w8) (GF := GF) DFrac.discard
  imod msgPtsC_of_struct «$a0_ptr» (⟨zero_val _, pty, null, «$v1_ptr», null, null, null,
      slice.mk slp (W64 1) (W64 1), null, null, null, null, null, slice.nil, slice.nil, slice.nil,
      0⟩ : raftpb.Message) (DFrac.own 1) false [l0]
      ⟨{ (zero_val MessageM) with Type' := W32 2, From' := id }, [propEntryM data], none, [], []⟩
      ⊤ rfl $$ [«$a0» Hsl] with Hm
  · iframe «$a0» Hsl Hnilb cTy cFr
    msg_nulls
    simp only [Bool.false_eq_true, ↓reduceIte, snapOpt]
    iframe He
    isplitl []; · iapply entsBig_nil
    isplitl []; · iempintro
    isplitl []; · ipureintro; trivial
    iapply ownSlice_nil
  have HmC : needsCap ({ (zero_val MessageM) with Type' := W32 2, From' := id } : MessageM) = false := rfl
  imod rdCred_zero_upd (GF := GF) γ with Hcr
  wp_apply wp_raft_Step cf _ γ _ id s «$a0_ptr» ({ (zero_val MessageM) with Type' := W32 2, From' := id } : MessageM)
    [propEntryM data] [] none []
    (by simp [StepMsg, stepMsgTypes, MsgProp])
    (by msg_ne) (by msg_ne)
    (by msg_ne) (by msg_ne)
    (by msg_ne) (by msg_ne)
    (by msg_ne) (by msg_ne)
    (by msg_ne) (by msg_ne)
    (by msg_ne)
    (fun _ => ⟨rfl, .inr rfl⟩) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne)
    (RestMsgOk.of_ne ⟨by msg_ne, by msg_ne, by msg_ne, by msg_ne, by msg_ne⟩) Hwf
    (GMode.Pre.of_facts Hpf (by msg_ne) (by msg_ne)) (fun h => absurd h (by msg_ne))
    $$ [$Hphys $Hghost $Hlc1 Hm Htk Hcr]
  · -- the message: its one-entry batch, the slots owned; `Context` nil
    simp only [MsgProp, ite_true]
    isplitl [Hm Htk]
    · simp only [named]
      isplitl [Hm]
      · simp only [msgIn, HmC]; iexact Hm
      isplitl [Htk]
      · isplitr
        · iexists ([propEntryM data].map fun _ => none)
          iapply ccEntsOk_normal [propEntryM data]
          intro e He
          simp only [List.mem_singleton] at He
          subst He
          rfl
        iapply (BigSepL.bigSepL_singleton (Φ := fun _ e => entTk (GF := GF) γ e)).2
        iexact Htk
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
    · rw [ite_eq_right (by msg_ne)]; iexact Hcr
    · imodintro
      iintro %Hc
      simp [MsgSnap] at Hc
  simp only [MsgProp]
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
