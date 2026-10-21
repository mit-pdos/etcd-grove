/-
Lemmas of the `node` API (`node.go`; raft v3.7 retarget, stage R5 phase 3, group G3).

* `msgIn_of_scalar_struct`: a fresh `&pb.Message{...}` setting only scalar fields (cells),
  its `Entries`, `Context`, `Responses` nil and no snapshot, is a received message (`msgIn`, at
  `□`), with no entries (`ReportUnreachable`, `ReportSnapshot`, `TransferLeadership`,
  `ForgetLeader`, `Campaign`).
* `msgPtsC_nn`: a message's pointer is not `nil`.
* `stepP_split`: `node.Step`'s argument opened: its message (`msgIn`, at `□` from the network,
  at `1` forwarded), of a nonnegative type (for `IsLocalMsg`), and the rest to close it again.
* `ownCCV2_persist`: a conf change frozen read-only (`node.ApplyConfChange` sends `AsV2`'s fresh
  one on `confc`, `confcP` holding it at `□`). A predicate lemma that belongs beside
  `ownCCV2` (`InvPb.lean`), as its instance `ownCCV2_discard_persistent`.
-/
module

public import RaftWitness.Proof.go_etcd_io.raft.v3.InvPbMsg
public import RaftWitness.Proof.go_etcd_io.raft.v3.InvNode

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

/-- `node.Step`'s argument opened (see the file header). -/
theorem stepP_split (γ : NodeNames) (id : w64) (ml : Loc) :
    stepP (GF := GF) γ id ml ⊢ ∃ (dqe : DFrac) (st : MsgSt), msgIn ml dqe st ∗
      ⌜0 ≤ sint.Z st.msg.Type'⌝ ∗ (msgIn ml dqe st -∗ stepP γ id ml) := by
  iintro H
  unfold stepP
  icases H with (Hnet | Hfwd)
  · iunfold netP at Hnet
    icases Hnet with ⟨%st, Hm, %Hok, %Hpvb, #Hab, #Hlb, Hcr, Htc⟩
    iexists DFrac.discard, st
    iframe Hm
    isplitr
    · ipureintro; exact netStepTypes_nonneg Hok.1
    iintro Hm
    ileft
    iunfold netP
    iexists st
    iframe Hm Hab Hlb Hcr Htc
    ipureintro; exact ⟨Hok, Hpvb⟩
  · iunfold fwdP at Hfwd
    icases Hfwd with ⟨%st, Hm, %Hty, #Hab, Htk⟩
    iexists DFrac.own 1, st
    iframe Hm
    isplitr
    · ipureintro; rw [Hty]; decide
    iintro Hm
    iright
    iunfold fwdP
    iexists st
    iframe Hm Hab Htk
    ipureintro; exact Hty

instance ownCCV2_discard_persistent (p : Loc) (m : CCV2M) :
    Persistent (ownCCV2 (GF := GF) p DFrac.discard m) := by
  unfold ownCCV2; infer_instance

/-- A conf change frozen read-only (see the file header). -/
theorem ownCCV2_persist (p : Loc) (dq : DFrac) (m : CCV2M) :
    ownCCV2 (GF := GF) p dq m ⊢ |==> ownCCV2 p DFrac.discard m := by
  iintro H
  iunfold ownCCV2 at H
  iNamed H
  imod (typedPointsto_dfractional (GF := GF) _ pt).dfractional_persist _ $$ HT with #HT
  imod (typedPointsto_dfractional (GF := GF) _ chs).dfractional_persist _ $$ HCh with #HCh
  imod (ownSlice_dfractional (GF := GF) _ _).dfractional_persist _ $$ Hch with #Hch
  imod (typedPointsto_dfractional (GF := GF) _ cs).dfractional_persist _ $$ HC with #HC
  imodintro
  iunfold ownCCV2
  iexists pt, chs, ls, cs, uf
  isplitr
  · ipureintro; exact Hnn
  iframe HT cT HCh Hch Hccs HC Hcs Hpb

end lemmas

end EtcdGrove
end Perennial
