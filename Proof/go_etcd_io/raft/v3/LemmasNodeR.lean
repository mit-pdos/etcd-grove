/-
Lemmas of the `node` API (`node.go`; raft v3.7 retarget, stage R5 phase 3, group G3).

* `msgIn_of_scalar_struct`: a fresh `&pb.Message{...}` setting only scalar fields (cells),
  its `Entries`, `Context`, `Responses` nil and no snapshot, is a received message (`msgIn`, at
  `□`), with no entries (`ReportUnreachable`, `ReportSnapshot`, `TransferLeadership`,
  `ForgetLeader`, `Campaign`).
* `msgPtsC_nn`: a message's pointer is not `nil`.
* `stepP_split`: `node.Step`'s argument opened: its message (`msgIn`, at `□` from the network,
  at `1` forwarded), of a nonnegative type (for `IsLocalMsg`), and the rest to close it again.
* `ownConfChangeV2_persist`: a conf change frozen read-only (`node.ApplyConfChange` sends `AsV2`'s fresh
  one on `confc`, `confcP` holding it at `□`). A predicate lemma that belongs beside
  `ownConfChangeV2` (`InvPb.lean`), as its instance `ownConfChangeV2_discard_persistent`.
-/
module

public import Proof.go_etcd_io.raft.v3.InvPbMsg
public import Proof.go_etcd_io.raft.v3.InvNodeChan
public import Proof.go_etcd_io.raft.v3.InvRawnodeReady
public import Proof.go_etcd_io.raft.v3.InvApplyConf
public import Spec.go_etcd_io.raft.v3.RawNode__ProposeConfChange

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
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
  sorry -- PHASE1
  /- PHASE1-OLD
 by
  iintro H
  unfold stepP
  icases H with (Hnet | Hfwd)
  · iunfold netP at Hnet
    icases Hnet with (⟨%st, Hm, %Hok, %Hpvb, #Hab, #Hsn, #Hlb, Hcr, Htc⟩ | Hhup)
    rotate_left
    · -- (2026-10-29, stage U7) `Campaign`'s `MsgHup`
      iunfold hupP at Hhup
      icases Hhup with ⟨Hm, Htc⟩
      iexists DFrac.discard, hupSt
      iframe Hm
      isplitr
      · ipureintro; simp [hupSt]
      iintro Hm
      ileft
      iapply netP_hup γ id ml $$ Hm Htc
    iexists DFrac.discard, st
    iframe Hm
    isplitr
    · ipureintro; exact netStepTypes_nonneg Hok.1
    iintro Hm
    ileft
    iunfold netP
    ileft
    iexists st
    iframe Hm Hab Hsn Hlb Hcr Htc
    ipureintro; exact ⟨Hok, Hpvb⟩
  · iunfold fwdP at Hfwd
    icases Hfwd with ⟨%st, Hm, %Hty, #Hab, Htk⟩
    iexists DFrac.own 1, st
    iframe Hm
    isplitr
    · ipureintro; rw [Hty.1]; decide
    iintro Hm
    iright
    iunfold fwdP
    iexists st
    iframe Hm Hab Htk
    ipureintro; exact Hty
  -/

instance ownConfChangeV2_discard_persistent (p : Loc) (m : ConfChangeV2M) :
    Persistent (ownConfChangeV2 (GF := GF) p DFrac.discard m) := by
  unfold ownConfChangeV2; infer_instance

/-- A conf change frozen read-only (see the file header). -/
theorem ownConfChangeV2_persist (p : Loc) (dq : DFrac) (m : ConfChangeV2M) :
    ownConfChangeV2 (GF := GF) p dq m ⊢ |==> ownConfChangeV2 p DFrac.discard m := by
  iintro H
  iunfold ownConfChangeV2 at H
  iNamed H
  imod (typedPointsto_dfractional (GF := GF) _ pt).dfractional_persist _ $$ HT with #HT
  imod (typedPointsto_dfractional (GF := GF) _ chs).dfractional_persist _ $$ HCh with #HCh
  imod (ownSlice_dfractional (GF := GF) _ _).dfractional_persist _ $$ Hch with #Hch
  imod (typedPointsto_dfractional (GF := GF) _ cs).dfractional_persist _ $$ HC with #HC
  imodintro
  iunfold ownConfChangeV2
  iexists pt, chs, ls, cs, uf
  isplitr
  · ipureintro; exact Hnn
  iframe HT cT HCh Hch Hccs HC Hcs Hpb

end lemmas

end EtcdGrove
end Perennial
