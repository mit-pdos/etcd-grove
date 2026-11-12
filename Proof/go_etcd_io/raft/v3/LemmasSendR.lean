/-
Lemmas of group G2 of stage R4 phase 3 (send, replication, snapshots, configuration, the role
changes, `newRaft`): building the messages raft sends.
-/
module

public import Proof.go_etcd_io.raft.v3.InvPbMsg
public import Proof.go_etcd_io.raft.v3.MsgOwnZ

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- A freshly allocated `&pb.Message{...}` without `Entries`, `Snapshot` and `Responses` (each
nil), its `Context` read-only bytes `ctx` (`slice.nil`, `[]` for most): an owned message holding
`mm`. -/
theorem msgOwn_lit (l : Loc) (v : raftpb.Message) (mm : MessageM) (ctx : List w8) (E : CoPset) :
    (⌜v.Entries' = slice.nil ∧ v.Snapshot' = null ∧ v.Responses' = slice.nil ∧
      v.unknownFields' = slice.nil⌝ ∗ l ↦ v ∗ v.Context' ↦*□ ctx ∗ cellRO v.Type' mm.Type' ∗ cellRO v.To' mm.To' ∗
      cellRO v.From' mm.From' ∗ cellRO v.Term' mm.Term' ∗
      cellRO v.LogTerm' mm.LogTerm' ∗ cellRO v.Index' mm.Index' ∗
      cellRO v.Commit' mm.Commit' ∗ cellRO v.Vote' mm.Vote' ∗
      cellRO v.Reject' mm.Reject' ∗ cellRO v.RejectHint' mm.RejectHint' : IProp GF) ⊢
      |={E}=> msgOwn l (DFrac.own 1) ⟨mm, [], none, ctx, []⟩ := by
  iintro ⟨%Hv, Hl, #Hcx, #cTy, #cTo, #cFr, #cTe, #cLt, #cIx, #cCo, #cVo, #cRj, #cRh⟩
  obtain ⟨Hes, Hsn, Hrs, Hu⟩ := Hv
  ihave Hnil : (slice.nil ↦* ([] : List Loc) : IProp GF) $$ []
  · iapply ownSlice_nil
  imod ownSlice_persist $$ Hnil with #Hnil
  ihave Hnilr : (slice.nil ↦* ([] : List Loc) : IProp GF) $$ []
  · iapply ownSlice_nil
  iapply msgOwn_of_struct l v [] _ E Hu
  iframe Hl cTy cTo cFr cTe cLt cIx cCo cVo cRj cRh Hcx
  rw [Hes, Hsn, Hrs]
  simp only [snapOpt]
  iframe Hnil Hnilr
  iapply BigSepL2.bigSepL2_nil.2; itrivial

/-- `msgOwn_lit` with no `Context` either. -/
theorem msgOwn_lit0 (l : Loc) (v : raftpb.Message) (mm : MessageM) (E : CoPset) :
    (⌜v.Entries' = slice.nil ∧ v.Snapshot' = null ∧ v.Responses' = slice.nil ∧
      v.unknownFields' = slice.nil ∧ v.Context' = slice.nil⌝ ∗ l ↦ v ∗
      cellRO v.Type' mm.Type' ∗ cellRO v.To' mm.To' ∗
      cellRO v.From' mm.From' ∗ cellRO v.Term' mm.Term' ∗
      cellRO v.LogTerm' mm.LogTerm' ∗ cellRO v.Index' mm.Index' ∗
      cellRO v.Commit' mm.Commit' ∗ cellRO v.Vote' mm.Vote' ∗
      cellRO v.Reject' mm.Reject' ∗ cellRO v.RejectHint' mm.RejectHint' : IProp GF) ⊢
      |={E}=> msgOwn l (DFrac.own 1) ⟨mm, [], none, [], []⟩ := by
  iintro ⟨%Hv, Hl, #cTy, #cTo, #cFr, #cTe, #cLt, #cIx, #cCo, #cVo, #cRj, #cRh⟩
  obtain ⟨Hes, Hsn, Hrs, Hu, Hcx⟩ := Hv
  ihave Hnilb : (slice.nil ↦* ([] : List w8) : IProp GF) $$ []
  · iapply ownSlice_nil
  imod ownSlice_persist $$ Hnilb with #Hnilb
  iapply msgOwn_lit l v mm [] E
  rw [Hcx]
  iframe Hl cTy cTo cFr cTe cLt cIx cCo cVo cRj cRh Hnilb
  ipureintro; exact ⟨Hes, Hsn, Hrs, Hu⟩

/-- (out_size C3) `msgOwn_lit`, held at a content (`msgOwnZ`, under any flag): the fresh literal has
no unknown fields, entries, snapshot or responses, so its size is its header's, bounded when its
context is at most `entBytesMax` bytes. -/
theorem msgOwnZ_lit (sz : Bool) (l : Loc) (v : raftpb.Message) (mm : MessageM) (ctx : List w8)
    (E : CoPset) (Hctx : ctx.length ≤ entBytesMax) :
    (⌜v.Entries' = slice.nil ∧ v.Snapshot' = null ∧ v.Responses' = slice.nil ∧
      v.unknownFields' = slice.nil⌝ ∗ l ↦ v ∗ v.Context' ↦*□ ctx ∗ cellRO v.Type' mm.Type' ∗ cellRO v.To' mm.To' ∗
      cellRO v.From' mm.From' ∗ cellRO v.Term' mm.Term' ∗
      cellRO v.LogTerm' mm.LogTerm' ∗ cellRO v.Index' mm.Index' ∗
      cellRO v.Commit' mm.Commit' ∗ cellRO v.Vote' mm.Vote' ∗
      cellRO v.Reject' mm.Reject' ∗ cellRO v.RejectHint' mm.RejectHint' : IProp GF) ⊢
      |={E}=> msgOwnZ sz l (DFrac.own 1) ⟨mm, [], none, ctx, []⟩ := by
  iintro ⟨%Hv, Hl, #Hcx, #cTy, #cTo, #cFr, #cTe, #cLt, #cIx, #cCo, #cVo, #cRj, #cRh⟩
  obtain ⟨Hes, Hsn, Hrs, Hu⟩ := Hv
  ihave Hnil : (slice.nil ↦* ([] : List Loc) : IProp GF) $$ []
  · iapply ownSlice_nil
  imod ownSlice_persist $$ Hnil with #Hnil
  ihave Hnilr : (slice.nil ↦* ([] : List Loc) : IProp GF) $$ []
  · iapply ownSlice_nil
  imod msgOwn_of_struct_uf l v [] ⟨mm, [], none, ctx, []⟩ E Hu $$ [Hl Hnilr] with ⟨Hm, #Hp⟩
  · iframe Hl cTy cTo cFr cTe cLt cIx cCo cVo cRj cRh Hcx
    rw [Hes, Hsn, Hrs]
    simp only [snapOpt]
    iframe Hnil Hnilr
    iapply BigSepL2.bigSepL2_nil.2; itrivial
  imodintro
  iapply msgOwnZ_of_uf sz l (DFrac.own 1) _ ⟨rfl, fun _ => ⟨rfl, rfl, Hctx⟩⟩
  iframe Hm Hp

/-- `msgOwnZ_lit` with no `Context` either. -/
theorem msgOwnZ_lit0 (sz : Bool) (l : Loc) (v : raftpb.Message) (mm : MessageM) (E : CoPset) :
    (⌜v.Entries' = slice.nil ∧ v.Snapshot' = null ∧ v.Responses' = slice.nil ∧
      v.unknownFields' = slice.nil ∧ v.Context' = slice.nil⌝ ∗ l ↦ v ∗
      cellRO v.Type' mm.Type' ∗ cellRO v.To' mm.To' ∗
      cellRO v.From' mm.From' ∗ cellRO v.Term' mm.Term' ∗
      cellRO v.LogTerm' mm.LogTerm' ∗ cellRO v.Index' mm.Index' ∗
      cellRO v.Commit' mm.Commit' ∗ cellRO v.Vote' mm.Vote' ∗
      cellRO v.Reject' mm.Reject' ∗ cellRO v.RejectHint' mm.RejectHint' : IProp GF) ⊢
      |={E}=> msgOwnZ sz l (DFrac.own 1) ⟨mm, [], none, [], []⟩ := by
  iintro ⟨%Hv, Hl, #cTy, #cTo, #cFr, #cTe, #cLt, #cIx, #cCo, #cVo, #cRj, #cRh⟩
  obtain ⟨Hes, Hsn, Hrs, Hu, Hcx⟩ := Hv
  ihave Hnilb : (slice.nil ↦* ([] : List w8) : IProp GF) $$ []
  · iapply ownSlice_nil
  imod ownSlice_persist $$ Hnilb with #Hnilb
  iapply msgOwnZ_lit sz l v mm [] E (by simp)
  rw [Hcx]
  iframe Hl cTy cTo cFr cTe cLt cIx cCo cVo cRj cRh Hnilb
  ipureintro; exact ⟨Hes, Hsn, Hrs, Hu⟩

omit [GooseSemantics] [GooseInterp] go_gctx sem package_sem in
/-- (out_size C3) A campaign's context is short. -/
theorem transferCtx_len (t : CampaignType) : (transferCtx t).length ≤ entBytesMax := by
  unfold transferCtx
  split
  · simp only [campaignTransfer, entBytesMax]; decide
  · simp

end lemmas

/-- Close the side goal of `msgOwn_lit` once its hypotheses are framed: the cells the literal
leaves `nil` hold zero (`cellRO_null`). -/
macro "msg_nulls" : tactic => `(tactic| (
  repeat (first
    | (isplitr; · (iunfold cellRO; ileft; ipureintro; exact ⟨rfl, rfl⟩))
    | (iunfold cellRO; ileft; ipureintro; exact ⟨rfl, rfl⟩))))

end EtcdGrove
end Perennial
