/-
The message predicates of the raft layer (raft v3.7 retarget, stage R4: `notes/decisions.md`,
"`raft.go` over pointer messages: the outbox owned, `Step` takes the message"), on top of
`InvPb.lean`'s `msgPtsC`/`msgPts`/`msgOwn`/`msgIn` and `InvPbLog.lean`'s snapshot persistence:

* a message built by raft (`&pb.Message{...}`) is owned (`msgPtsC_of_struct`, `msgOwn_of_struct`);
* a message `Step` receives, `msgIn`, becomes an owned message (`msgIn_to_msgOwn`: its capacity
  dropped, its `Entries` elements frozen), e.g. to be forwarded (`stepFollower`);
* an owned message is frozen read-only for good (`msgOwn_persist`; `msgOwn l □ st` is
  persistent): a stored read-index request (`readOnly`'s, `pendingReadIndexMessages`);
* the field stores raft makes into a message it owns: `From` and `Term` (`send`), `To`
  (`stepFollower`), each a fresh cell (`msgPtsC_store_From`, `_Term`, `_To`). The `Entries`
  slots `stepLeader` replaces go through `GetEntries`' spec (its wand takes any entries back).
-/
module

public import Raft37.Proof.go_etcd_io.raft.v3.InvPbLog

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

open Iris.ProofMode

/-! ### Snapshots of messages -/

instance snapOpt_persistent (p : Loc) (o : Option SnapshotM) :
    Persistent (snapOpt (GF := GF) p DFrac.discard o) := by
  rcases o with _ | sn <;> unfold snapOpt <;> infer_instance

theorem snapOpt_persist (p : Loc) (dq : DFrac) (o : Option SnapshotM) :
    snapOpt (GF := GF) p dq o ⊢ |==> snapOpt p DFrac.discard o := by
  rcases o with _ | sn
  · simp only [snapOpt]; iintro %H; imodintro; ipureintro; exact H
  · simp only [snapOpt]; iapply ownSnapM_persist

/-! ### Messages -/

/-- A frozen message is persistent. (Instance search on the unfolded 16-variable body fails
outright; the existentials and conjunctions are taken apart one by one.) -/
instance msgOwn_persistent (l : Loc) (ms : MsgSt) :
    Persistent (msgOwn (GF := GF) l DFrac.discard ms) := by
  simp only [msgOwn, msgPts]; unfold msgPtsC
  simp only [Bool.false_eq_true, ↓reduceIte]
  repeat (first
    | infer_instance
    | (refine @exists_persistent _ _ _ _ ?_; intro _)
    | refine @sep_persistent _ _ _ _ ?_ ?_)

/-- Forget the capacity. -/
theorem msgPtsC_drop_cap (l : Loc) (dq dqe : DFrac) (cap : Bool) (ms : MsgSt) :
    msgPtsC (GF := GF) l dq dqe cap ms ⊢ msgPts l dq dqe ms := by
  iintro H
  iNamed H
  iclear Hes_cap
  simp only [msgPts]
  iunfold msgPtsC
  iexists pty, pto, pfr, pte, plt, pix, pco, pvo, prj, prh, es, els, ps, cs, rs, uf
  isplitr
  · ipureintro; exact Hnn
  iframe
  iframe cTy cTo cFr cTe cLt cIx cCo cVo cRj cRh Hents Hcs Hpb
  simp only [named, Bool.false_eq_true, ↓reduceIte]; iempintro

/-- A message's `Entries` elements frozen read-only, its capacity dropped: what raft makes of a
message it received (`msgIn`, `dqe = 1` for a proposal) before it queues or stores it. -/
theorem msgPtsC_to_msgOwn (l : Loc) (dq dqe : DFrac) (cap : Bool) (ms : MsgSt) :
    msgPtsC (GF := GF) l dq dqe cap ms ⊢ |==> msgOwn l dq ms := by
  iintro H
  iNamed H
  iclear Hes_cap
  imod (ownSlice_dfractional (GF := GF) _ _).dfractional_persist _ $$ Hes with #Hes
  imodintro
  simp only [msgOwn, msgPts]
  iunfold msgPtsC
  iexists pty, pto, pfr, pte, plt, pix, pco, pvo, prj, prh, es, els, ps, cs, rs, uf
  isplitr
  · ipureintro; exact Hnn
  iframe
  iframe cTy cTo cFr cTe cLt cIx cCo cVo cRj cRh Hes Hents Hcs Hpb
  simp only [named, Bool.false_eq_true, ↓reduceIte]; iempintro

/-- A received message (`Step`'s `msgIn`) as an owned message (stage R4, Q3): forwarded by
`stepFollower`, queued by `send`. -/
theorem msgIn_to_msgOwn (l : Loc) (dqe : DFrac) (ms : MsgSt) :
    msgIn (GF := GF) l dqe ms ⊢ |==> msgOwn l (DFrac.own 1) ms :=
  msgPtsC_to_msgOwn l _ dqe true ms

/-- An owned message frozen read-only for good (a stored read-index request: nothing writes it
after, `responseToReadIndexReq` reads `From` and shares `Entries`). -/
theorem msgOwn_persist (l : Loc) (dq : DFrac) (ms : MsgSt) :
    msgOwn (GF := GF) l dq ms ⊢ |==> msgOwn l DFrac.discard ms := by
  iintro H
  simp only [msgOwn, msgPts]
  iNamed H
  iclear Hes_cap
  imod (typedPointsto_dfractional (GF := GF) _ pty).dfractional_persist _ $$ HTy with #HTy
  imod (typedPointsto_dfractional (GF := GF) _ pto).dfractional_persist _ $$ HTo with #HTo
  imod (typedPointsto_dfractional (GF := GF) _ pfr).dfractional_persist _ $$ HFr with #HFr
  imod (typedPointsto_dfractional (GF := GF) _ pte).dfractional_persist _ $$ HTe with #HTe
  imod (typedPointsto_dfractional (GF := GF) _ plt).dfractional_persist _ $$ HLt with #HLt
  imod (typedPointsto_dfractional (GF := GF) _ pix).dfractional_persist _ $$ HIx with #HIx
  imod (typedPointsto_dfractional (GF := GF) _ pco).dfractional_persist _ $$ HCo with #HCo
  imod (typedPointsto_dfractional (GF := GF) _ pvo).dfractional_persist _ $$ HVo with #HVo
  imod (typedPointsto_dfractional (GF := GF) _ prj).dfractional_persist _ $$ HRj with #HRj
  imod (typedPointsto_dfractional (GF := GF) _ prh).dfractional_persist _ $$ HRh with #HRh
  imod (typedPointsto_dfractional (GF := GF) _ es).dfractional_persist _ $$ HEs with #HEs
  imod (typedPointsto_dfractional (GF := GF) _ ps).dfractional_persist _ $$ HSn with #HSn
  imod snapOpt_persist _ _ _ $$ Hsn with #Hsn
  imod (typedPointsto_dfractional (GF := GF) _ cs).dfractional_persist _ $$ HCx with #HCx
  imod (typedPointsto_dfractional (GF := GF) _ rs).dfractional_persist _ $$ HRs with #HRs
  imod (ownSlice_dfractional (GF := GF) _ _).dfractional_persist _ $$ Hrs with #Hrs
  imodintro
  iunfold msgPtsC
  iexists pty, pto, pfr, pte, plt, pix, pco, pvo, prj, prh, es, els, ps, cs, rs, uf
  isplitr
  · ipureintro; exact Hnn
  iframe HTy cTy HTo cTo HFr cFr HTe cTe HLt cLt HIx cIx HCo cCo HVo cVo HRj cRj HRh cRh
    HEs Hes Hents HSn Hsn HCx Hcs HRs Hrs Hpb
  simp only [named, Bool.false_eq_true, ↓reduceIte]; iempintro

/-- A freshly allocated `*pb.Message` (`&pb.Message{...}`, its hidden fields zero), its pointer
fields set to cells holding `ms.msg`'s scalars, its `Entries` to a slice of read-only entries
holding `ms.ents` (elements at `dqe`, the capacity when `cap`), its `Snapshot` to `ms.snap`'s,
its `Context` to read-only bytes and its `Responses` to `ms.resps`, is a message holding `ms`,
owned. -/
theorem msgPtsC_of_struct (l : Loc) (v : raftpb.Message) (dqe : DFrac) (cap : Bool)
    (els : List Loc) (ms : MsgSt) (E : CoPset) (Hu : v.unknownFields' = slice.nil) :
    (l ↦ v ∗ cellRO v.Type' ms.msg.Type' ∗ cellRO v.To' ms.msg.To' ∗
      cellRO v.From' ms.msg.From' ∗ cellRO v.Term' ms.msg.Term' ∗
      cellRO v.LogTerm' ms.msg.LogTerm' ∗ cellRO v.Index' ms.msg.Index' ∗
      cellRO v.Commit' ms.msg.Commit' ∗ cellRO v.Vote' ms.msg.Vote' ∗
      cellRO v.Reject' ms.msg.Reject' ∗ cellRO v.RejectHint' ms.msg.RejectHint' ∗
      v.Entries' ↦*{dqe} els ∗ ([∗list] p;e ∈ els;ms.ents, entRO p e) ∗
      (if cap then ownSliceCap Loc v.Entries' (DFrac.own 1) else emp) ∗
      snapOpt v.Snapshot' (DFrac.own 1) ms.snap ∗ v.Context' ↦*□ ms.ctx ∗
      v.Responses' ↦* ms.resps : IProp GF) ⊢
      |={E}=> msgPtsC l (DFrac.own 1) dqe cap ms := by
  iintro ⟨Hl, #cTy, #cTo, #cFr, #cTe, #cLt, #cIx, #cCo, #cVo, #cRj, #cRh, Hes, #Hents, Hes_cap,
    Hsn, #Hcs, Hrs⟩
  ihave %Hnn := typedPointsto_not_null $$ Hl
  icases typedPointsto_split _ _ _ $$ Hl with Hl
  simp only [TypedPointsto.typedPointstoDef]
  icases Hl with ⟨state, Ty, To, From, Term, LogTerm, Index, Entries, Commit, Vote, Snapshot,
    Reject, RejectHint, Context, Responses, unknownFields, sizeCache, -⟩
  rw [Hu]
  ihave Hnil : (slice.nil ↦* ([] : List w8) : IProp GF) $$ []
  · iapply ownSlice_nil
  imod pbMsg_alloc raftpb.Message l v.state' v.sizeCache' slice.nil [] E $$ [state sizeCache unknownFields Hnil] with #Hpb
  · iframe
  imodintro
  iunfold msgPtsC
  iexists v.Type', v.To', v.From', v.Term', v.LogTerm', v.Index', v.Commit', v.Vote', v.Reject',
    v.RejectHint', v.Entries', els, v.Snapshot', v.Context', v.Responses', []
  isplitr
  · ipureintro; exact Hnn
  iframe
  iframe cTy cTo cFr cTe cLt cIx cCo cVo cRj cRh Hents Hcs Hpb

/-- `msgPtsC_of_struct` for a message raft builds: its entries read-only, no capacity. -/
theorem msgOwn_of_struct (l : Loc) (v : raftpb.Message) (els : List Loc) (ms : MsgSt) (E : CoPset)
    (Hu : v.unknownFields' = slice.nil) :
    (l ↦ v ∗ cellRO v.Type' ms.msg.Type' ∗ cellRO v.To' ms.msg.To' ∗
      cellRO v.From' ms.msg.From' ∗ cellRO v.Term' ms.msg.Term' ∗
      cellRO v.LogTerm' ms.msg.LogTerm' ∗ cellRO v.Index' ms.msg.Index' ∗
      cellRO v.Commit' ms.msg.Commit' ∗ cellRO v.Vote' ms.msg.Vote' ∗
      cellRO v.Reject' ms.msg.Reject' ∗ cellRO v.RejectHint' ms.msg.RejectHint' ∗
      v.Entries' ↦*□ els ∗ ([∗list] p;e ∈ els;ms.ents, entRO p e) ∗
      snapOpt v.Snapshot' (DFrac.own 1) ms.snap ∗ v.Context' ↦*□ ms.ctx ∗
      v.Responses' ↦* ms.resps : IProp GF) ⊢
      |={E}=> msgOwn l (DFrac.own 1) ms := by
  iintro ⟨Hl, #cTy, #cTo, #cFr, #cTe, #cLt, #cIx, #cCo, #cVo, #cRj, #cRh, #Hes, #Hents,
    Hsn, #Hcs, Hrs⟩
  simp only [msgOwn, msgPts]
  iapply msgPtsC_of_struct l v DFrac.discard false els ms E Hu
  iframe
  iframe cTy cTo cFr cTe cLt cIx cCo cVo cRj cRh Hes Hents Hcs
  simp only [Bool.false_eq_true, ↓reduceIte]; iempintro

/-! ### Field stores (`send`'s `From`/`Term`, `stepFollower`'s `To`): a fresh cell each -/

/-- `m.From = new(r.id)` (`send`, `raft.go:516`). -/
theorem msgPtsC_store_From (l : Loc) (dqe : DFrac) (cap : Bool) (ms : MsgSt) :
    msgPtsC (GF := GF) l (DFrac.own 1) dqe cap ms ⊢
      ∃ p : Loc, l.[raftpb.Message, go!"From"] ↦ p ∗
        (∀ (p' : Loc) (v : w64), l.[raftpb.Message, go!"From"] ↦ p' -∗ cellRO p' v -∗
          msgPtsC l (DFrac.own 1) dqe cap { ms with msg := { ms.msg with From' := v } }) := by
  iintro H
  iNamed H
  iexists pfr
  iframe HFr
  iintro %p' %v HFr #cFr'
  iunfold msgPtsC
  iexists pty, pto, p', pte, plt, pix, pco, pvo, prj, prh, es, els, ps, cs, rs, uf
  isplitr
  · ipureintro; exact Hnn
  iframe
  iframe cTy cTo cFr' cTe cLt cIx cCo cVo cRj cRh Hents Hcs Hpb

/-- `m.Term = new(r.Term)` (`send`, `raft.go:543`). -/
theorem msgPtsC_store_Term (l : Loc) (dqe : DFrac) (cap : Bool) (ms : MsgSt) :
    msgPtsC (GF := GF) l (DFrac.own 1) dqe cap ms ⊢
      ∃ p : Loc, l.[raftpb.Message, go!"Term"] ↦ p ∗
        (∀ (p' : Loc) (v : w64), l.[raftpb.Message, go!"Term"] ↦ p' -∗ cellRO p' v -∗
          msgPtsC l (DFrac.own 1) dqe cap { ms with msg := { ms.msg with Term' := v } }) := by
  iintro H
  iNamed H
  iexists pte
  iframe HTe
  iintro %p' %v HTe #cTe'
  iunfold msgPtsC
  iexists pty, pto, pfr, p', plt, pix, pco, pvo, prj, prh, es, els, ps, cs, rs, uf
  isplitr
  · ipureintro; exact Hnn
  iframe
  iframe cTy cTo cFr cTe' cLt cIx cCo cVo cRj cRh Hents Hcs Hpb

/-- `m.To = new(r.lead)` (`stepFollower` forwarding a proposal, a read index or a leader
transfer, `raft.go:1720`, `1739`, `1761`). -/
theorem msgPtsC_store_To (l : Loc) (dqe : DFrac) (cap : Bool) (ms : MsgSt) :
    msgPtsC (GF := GF) l (DFrac.own 1) dqe cap ms ⊢
      ∃ p : Loc, l.[raftpb.Message, go!"To"] ↦ p ∗
        (∀ (p' : Loc) (v : w64), l.[raftpb.Message, go!"To"] ↦ p' -∗ cellRO p' v -∗
          msgPtsC l (DFrac.own 1) dqe cap { ms with msg := { ms.msg with To' := v } }) := by
  iintro H
  iNamed H
  iexists pto
  iframe HTo
  iintro %p' %v HTo #cTo'
  iunfold msgPtsC
  iexists pty, p', pfr, pte, plt, pix, pco, pvo, prj, prh, es, els, ps, cs, rs, uf
  isplitr
  · ipureintro; exact Hnn
  iframe
  iframe cTy cTo' cFr cTe cLt cIx cCo cVo cRj cRh Hents Hcs Hpb

end lemmas

end EtcdGrove
end Perennial
