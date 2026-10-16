/-
Lemmas of the `node` API (`node.go`; raft v3.7 retarget, stage R5 phase 3, group G3).

* `msgIn_of_scalar_struct`: a fresh `&pb.Message{...}` setting only scalar fields (cells),
  its `Entries`, `Context`, `Responses` nil and no snapshot, is a received message (`msgIn`, at
  `□`), with no entries (`ReportUnreachable`, `ReportSnapshot`, `TransferLeadership`,
  `ForgetLeader`, `Campaign`).
* `msgPtsC_nonnull`: a message's pointer is not `nil`.
* `stepP_split`: `node.Step`'s argument opened: its message (`msgIn`, at `□` from the network,
  at `1` forwarded), of a nonnegative type (for `IsLocalMsg`), and the rest to close it again.
-/
module

public import Raft37.Proof.go_etcd_io.raft.v3.InvPbMsg
public import Raft37.Proof.go_etcd_io.raft.v3.InvNode

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
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

/-- A message's pointer is not `nil`. -/
theorem msgPtsC_nonnull (l : Loc) (dq dqe : DFrac) (cap : Bool) (ms : MsgSt) :
    msgPtsC (GF := GF) l dq dqe cap ms ⊢ ⌜l ≠ null⌝ ∗ msgPtsC l dq dqe cap ms := by
  iintro H
  ihave %Hnn : ⌜l ≠ null⌝ $$ [H]
  · iunfold msgPtsC at H
    iNamed H
    ipureintro; exact Hnn
  iframe H
  ipureintro; exact Hnn

/-- `node.Step`'s argument opened (see the file header). -/
theorem stepP_split (γ : NodeNames) (id : w64) (ml : Loc) :
    stepP (GF := GF) γ id ml ⊢ ∃ (dqe : DFrac) (st : MsgSt), msgIn ml dqe st ∗
      ⌜0 ≤ sint.Z st.msg.Type'⌝ ∗ (msgIn ml dqe st -∗ stepP γ id ml) := by
  iintro H
  unfold stepP
  icases H with (Hnet | Hfwd)
  · iunfold netP at Hnet
    icases Hnet with ⟨%st, Hm, %Hok, #Hab, #Hlb, Hcr, Htc⟩
    iexists DFrac.discard, st
    iframe Hm
    isplitr
    · ipureintro; exact netStepTypes_nonneg Hok.1
    iintro Hm
    ileft
    iunfold netP
    iexists st
    iframe Hm Hab Hlb Hcr Htc
    ipureintro; exact Hok
  · iunfold fwdP at Hfwd
    icases Hfwd with ⟨%st, Hm, %Hty, #Hab⟩
    iexists DFrac.own 1, st
    iframe Hm
    isplitr
    · ipureintro; rw [Hty]; decide
    iintro Hm
    iright
    iunfold fwdP
    iexists st
    iframe Hm Hab
    ipureintro; exact Hty

end lemmas

end EtcdGrove
end Perennial
