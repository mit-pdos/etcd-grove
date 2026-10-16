/-
Lemmas of group G2 of stage R4 phase 3 (send, replication, snapshots, configuration, the role
changes, `newRaft`): building the messages raft sends.
-/
module

public import Raft37.Proof.go_etcd_io.raft.v3.InvPbMsg

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
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

end lemmas

/-- Close the side goal of `msgOwn_lit` once its hypotheses are framed: the cells the literal
leaves `nil` hold zero (`cellRO_null`). -/
macro "msg_nulls" : tactic => `(tactic| (
  repeat (first
    | (isplitr; · (iunfold cellRO; ileft; ipureintro; exact ⟨rfl, rfl⟩))
    | (iunfold cellRO; ileft; ipureintro; exact ⟨rfl, rfl⟩))))

end EtcdGrove
end Perennial
