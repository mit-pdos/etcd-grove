/-
Lemmas of the `node` API (`node.go`; raft v3.7 retarget, stage R5 phase 3, group G3).

* `msgIn_of_scalar_struct`: a fresh `&pb.Message{...}` setting only scalar fields (cells),
  its `Entries`, `Context`, `Responses` nil and no snapshot, is a received message (`msgIn`, at
  `□`), with no entries (`ReportUnreachable`, `ReportSnapshot`, `TransferLeadership`,
  `ForgetLeader`, `Campaign`).
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

/-- A fresh message setting only scalar fields (see the file header): its struct as
`&pb.Message{...}` allocates it, the pointer fields given. -/
theorem msgIn_of_scalar_struct (l : Loc) (pty pto pfr pTerm plt pix pco pvo prj prh : Loc)
    (m : MessageM) (E : CoPset) :
    (l ↦ ({ state' := zeroValDef, Type' := pty, To' := pto, From' := pfr,
                Term' := pTerm, LogTerm' := plt, Index' := pix, Entries' := slice.nil,
                Commit' := pco, Vote' := pvo, Snapshot' := null, Reject' := prj,
                RejectHint' := prh, Context' := slice.nil, Responses' := slice.nil,
                unknownFields' := slice.nil, sizeCache' := 0 } : raftpb.Message) ∗
      cellRO pty m.Type' ∗ cellRO pto m.To' ∗
      cellRO pfr m.From' ∗ cellRO pTerm m.Term' ∗
      cellRO plt m.LogTerm' ∗ cellRO pix m.Index' ∗
      cellRO pco m.Commit' ∗ cellRO pvo m.Vote' ∗
      cellRO prj m.Reject' ∗ cellRO prh m.RejectHint' : IProp GF) ⊢
      |={E}=> msgIn l DFrac.discard ⟨m, [], none, [], []⟩ := by
  iintro ⟨Hl, #cTy, #cTo, #cFr, #cTe, #cLt, #cIx, #cCo, #cVo, #cRj, #cRh⟩
  ihave Hnilb : (slice.nil ↦* ([] : List w8) : IProp GF) $$ []
  · iapply ownSlice_nil
  imod ownSlice_persist $$ Hnilb with #Hnilb
  ihave Hnile : (slice.nil ↦* ([] : List Loc) : IProp GF) $$ []
  · iapply ownSlice_nil
  imod ownSlice_persist $$ Hnile with #Hnile
  ihave Hnilr : (slice.nil ↦* ([] : List Loc) : IProp GF) $$ []
  · iapply ownSlice_nil
  imod msgPtsC_of_struct l
      { state' := zeroValDef, Type' := pty, To' := pto, From' := pfr,
        Term' := pTerm, LogTerm' := plt, Index' := pix, Entries' := slice.nil,
        Commit' := pco, Vote' := pvo, Snapshot' := null, Reject' := prj,
        RejectHint' := prh, Context' := slice.nil, Responses' := slice.nil,
        unknownFields' := slice.nil, sizeCache' := 0 }
      DFrac.discard true [] ⟨m, [], none, [], []⟩ E rfl
      $$ [Hl Hnilr] with Hmsg
  · iframe Hl Hnile Hnilb Hnilr cTy cTo cFr cTe cLt cIx cCo cVo cRj cRh
    simp only [snapOpt, ↓reduceIte]
    isplitr
    · iapply BigSepL2.bigSepL2_nil.2; itrivial
    isplitr
    · iapply ownSliceCap_nil
    itrivial
  imodintro
  iapply msgIn_of_msgPtsC_cap $$ Hmsg

end lemmas

end EtcdGrove
end Perennial
