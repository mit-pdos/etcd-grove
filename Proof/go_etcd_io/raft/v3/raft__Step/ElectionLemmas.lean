/- The election branches' own helpers for `Step`'s proof (raft v3.7 retarget, stage R4 phase 3,
group G4a).

`raft.Step.Postulates` (`Base.lean`) bundles the callee specs of `raft.go`; since v3.7 `Step`
also reads the message through its protobuf getters (`m.GetTerm()`, ...) and builds responses
with `MessageType.Enum()`, whose specs (R1, `Spec/.../raftpb/`) are bundled here as
`raft.Step.PbPostulates`, which the election branch lemmas take beside `raft.Step.Postulates`.
-/
module

public import Proof.go_etcd_io.raft.v3.raft__Step.Base
public import Proof.go_etcd_io.raft.v3.InvPbMsg
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetType
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetTerm
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetFrom
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetLogTerm
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetIndex
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetReject
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetContext
public import Spec.go_etcd_io.raft.v3.raftpb.MessageType__Enum

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section base
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The protobuf specs `Step`'s election branches use (stage R4): the message getters and
`MessageType.Enum`. -/
structure raft.Step.PbPostulates : Prop where
  GetType : raftpb.Message.GetType.spec (GF := GF) (hG := hG)
  GetTerm : raftpb.Message.GetTerm.spec (GF := GF) (hG := hG)
  GetFrom : raftpb.Message.GetFrom.spec (GF := GF) (hG := hG)
  GetLogTerm : raftpb.Message.GetLogTerm.spec (GF := GF) (hG := hG)
  GetIndex : raftpb.Message.GetIndex.spec (GF := GF) (hG := hG)
  GetReject : raftpb.Message.GetReject.spec (GF := GF) (hG := hG)
  GetContext : raftpb.Message.GetContext.spec (GF := GF) (hG := hG)
  Enum : raftpb.MessageType.Enum.spec (GF := GF) (hG := hG)

/-- A message's pointer is not `nil` (kept). -/
theorem msgPtsC_nn (l : Loc) (dq dqe : DFrac) (cap : Bool) (ms : MsgSt) :
    msgPtsC (GF := GF) l dq dqe cap ms ⊢ ⌜l ≠ null⌝ ∗ msgPtsC l dq dqe cap ms := by
  iintro H
  ihave %Hnn : ⌜l ≠ null⌝ $$ [H]
  · iunfold msgPtsC at H
    iNamed H
    ipureintro; exact Hnn
  iframe H
  ipureintro; exact Hnn

/-- The request's `From` cell, for a response built with `To: m.From` (the cell is shared). -/
theorem msgPtsC_From_acc (l : Loc) (dq dqe : DFrac) (cap : Bool) (ms : MsgSt) :
    msgPtsC (GF := GF) l dq dqe cap ms ⊢
      ∃ p : Loc, l.[raftpb.Message, go!"From"] ↦{dq} p ∗ cellRO p ms.msg.From' ∗
        (l.[raftpb.Message, go!"From"] ↦{dq} p -∗ msgPtsC l dq dqe cap ms) := by
  iintro H
  iNamed H
  iexists pfr
  iframe HFr cFr
  iintro HFr
  iunfold msgPtsC
  iexists pty, pto, pfr, pte, plt, pix, pco, pvo, prj, prh, es, els, ps, cs, rs, uf
  isplitr
  · ipureintro; exact Hnn
  iframe
  iframe cTy cTo cFr cTe cLt cIx cCo cVo cRj cRh Hents Hcs Hpb

/-- The request's `Term` cell, for a response built with `Term: m.Term`. -/
theorem msgPtsC_Term_acc (l : Loc) (dq dqe : DFrac) (cap : Bool) (ms : MsgSt) :
    msgPtsC (GF := GF) l dq dqe cap ms ⊢
      ∃ p : Loc, l.[raftpb.Message, go!"Term"] ↦{dq} p ∗ cellRO p ms.msg.Term' ∗
        (l.[raftpb.Message, go!"Term"] ↦{dq} p -∗ msgPtsC l dq dqe cap ms) := by
  iintro H
  iNamed H
  iexists pte
  iframe HTe cTe
  iintro HTe
  iunfold msgPtsC
  iexists pty, pto, pfr, pte, plt, pix, pco, pvo, prj, prh, es, els, ps, cs, rs, uf
  isplitr
  · ipureintro; exact Hnn
  iframe
  iframe cTy cTo cFr cTe cLt cIx cCo cVo cRj cRh Hents Hcs Hpb

/-- The struct of `&pb.Message{To: .., Term: .., Type: .., Reject: ..}`. -/
abbrev respStruct (pty pto pte prj : Loc) : raftpb.Message :=
  { state' := zeroValDef, Type' := pty, To' := pto, From' := null,
    Term' := pte, LogTerm' := null, Index' := null, Entries' := slice.nil, Commit' := null,
    Vote' := null, Snapshot' := null, Reject' := prj, RejectHint' := null,
    Context' := slice.nil, Responses' := slice.nil, unknownFields' := slice.nil,
    sizeCache' := 0 }

/-- A response raft builds, `&pb.Message{To: .., Term: .., Type: .., Reject: ..}` (each set
field a cell; `Term`/`Reject` may be unset, `null`), is an owned message without entries,
snapshot, context or responses. -/
theorem msgOwn_of_resp (l pty pto pte prj : Loc) (ty : raftpb.MessageType) (to te : w64)
    (rj : Bool) (E : CoPset) :
    (l ↦ respStruct pty pto pte prj ∗
      cellRO pty ty ∗ cellRO pto to ∗ cellRO pte te ∗ cellRO prj rj : IProp GF) ⊢
      |={E}=> msgOwn l (DFrac.own 1)
        ⟨⟨ty, to, W64 0, te, W64 0, W64 0, W64 0, W64 0, rj, W64 0⟩, [], none, [], []⟩ := by
  iintro ⟨Hl, #cTy, #cTo, #cTe, #cRj⟩
  iapply (msgOwn_of_struct l (respStruct pty pto pte prj) [] _ E rfl)
  dsimp only
  iframe Hl
  iframe cTy cTo cTe cRj
  ihave #Hn64 : cellRO (GF := GF) null (W64 0) $$ []
  · iapply (show ⊢ cellRO (GF := GF) null (W64 0) from cellRO_null (V := w64))
  iframe Hn64
  isplitr
  · iapply ownSlice_nil
  isplitr
  · iapply BigSepL2.bigSepL2_nil.2; ipureintro; trivial
  isplitr
  · simp only [snapOpt]; ipureintro; trivial
  isplitr
  · iapply ownSlice_nil
  iapply ownSlice_nil

end base

set_option hygiene false in
/-- A getter call on the message `Hm`, by the specs `PB : raft.Step.PbPostulates` (both names
the caller's). -/
macro "wp_get" : tactic =>
  `(tactic| first
    | (wp_apply PB.GetTerm.1 $$ [Hm] as Hm; iexact Hm)
    | (wp_apply PB.GetType.1 $$ [Hm] as Hm; iexact Hm)
    | (wp_apply PB.GetFrom.1 $$ [Hm] as Hm; iexact Hm)
    | (wp_apply PB.GetLogTerm.1 $$ [Hm] as Hm; iexact Hm)
    | (wp_apply PB.GetIndex.1 $$ [Hm] as Hm; iexact Hm)
    | (wp_apply PB.GetReject.1 $$ [Hm] as Hm; iexact Hm))

/-- Every getter call (`wp_get`) and pure step up to the next other call or undecided test. -/
macro "wp_gets" : tactic => `(tactic| repeat (wp_get; try wp_auto))

end EtcdGrove
end Perennial
