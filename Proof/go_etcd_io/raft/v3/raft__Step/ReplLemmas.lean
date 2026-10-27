/- The callee specs of raft v3.7's `Step` beyond `raft.Step.Postulates` that the replication,
response, proposal, storage-acknowledgement and read-index branches use (stage R4 phase 3,
group G4b): the `*pb.Message`/`*pb.Entry` getters the body reads the message through, and
`MessageType.Enum` (`&pb.Message{..., Type: pb.MsgAppResp.Enum()}`).

`Base.lean`'s `raft.Step.Postulates` (shared) is unchanged: the branch lemmas take this structure
as a second argument (`_Q`), which the dispatch builds from `raft.Step.wp_proof`'s hypotheses. -/
module

public import Proof.go_etcd_io.raft.v3.raft__Step.Base
public import Proof.go_etcd_io.raft.v3.raft__Step.Dispatch
public import Proof.go_etcd_io.raft.v3.InvPbMsg
public import Proof.go_etcd_io.raft.v3.InvPbLog
public import Proof.go_etcd_io.raft.v3.LemmasMemstorage
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetType
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetTerm
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetFrom
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetTo
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetIndex
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetLogTerm
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetCommit
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetReject
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetEntries
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetSnapshot
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetContext
public import Spec.go_etcd_io.raft.v3.raftpb.Entry__GetIndex
public import Spec.go_etcd_io.raft.v3.raftpb.MessageType__Enum

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section base
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The raftpb callees of `Step`'s body (stage R4): the message's getters and `Enum`. (Group G4a's
`raft.Step.PbPostulates`, `ElectionLemmas.lean`, is the election branches' subset; this one, the
replication branches', adds `GetTo`, `GetCommit`, `GetEntries`, `GetSnapshot` and
`Entry.GetIndex`; same field names.) -/
structure raft.Step.ReplPbPostulates : Prop where
  GetType : raftpb.Message.GetType.spec (GF := GF) (hG := hG)
  GetTerm : raftpb.Message.GetTerm.spec (GF := GF) (hG := hG)
  GetFrom : raftpb.Message.GetFrom.spec (GF := GF) (hG := hG)
  GetTo : raftpb.Message.GetTo.spec (GF := GF) (hG := hG)
  GetIndex : raftpb.Message.GetIndex.spec (GF := GF) (hG := hG)
  GetLogTerm : raftpb.Message.GetLogTerm.spec (GF := GF) (hG := hG)
  GetCommit : raftpb.Message.GetCommit.spec (GF := GF) (hG := hG)
  GetReject : raftpb.Message.GetReject.spec (GF := GF) (hG := hG)
  GetEntries : raftpb.Message.GetEntries.spec (GF := GF) (hG := hG)
  GetSnapshot : raftpb.Message.GetSnapshot.spec (GF := GF) (hG := hG)
  GetContext : raftpb.Message.GetContext.spec (GF := GF) (hG := hG)
  EntryGetIndex : raftpb.Entry.GetIndex.spec (GF := GF) (hG := hG)
  Enum : raftpb.MessageType.Enum.spec (GF := GF) (hG := hG)

namespace StepProof

/-- A message `Step` received, off a proposal, as the `stepX` specs take it. (Over any
capacity flag `cap`, `msgIn`'s `needsCap st.msg`, so that it applies to a `msgIn` unfolded by a
generic `msgPtsC` lemma.) -/
theorem msgIn_nonprop {ml : Loc} {m : MessageM} {st : MsgSt} {cap : Bool} (h : m.Type' ≠ MsgProp) :
    msgPtsC (GF := GF) ml (DFrac.own 1) DFrac.discard cap st ⊢
      msgPtsC ml (DFrac.own 1) (if m.Type' = MsgProp then DFrac.own 1 else DFrac.discard) cap st := by
  simp only [h, ↓reduceIte]; exact .rfl

/-- A proposal `Step` received, as the `stepX` specs take it. -/
theorem msgIn_prop {ml : Loc} {m : MessageM} {st : MsgSt} {cap : Bool} (h : m.Type' = MsgProp) :
    msgPtsC (GF := GF) ml (DFrac.own 1) (DFrac.own 1) cap st ⊢
      msgPtsC ml (DFrac.own 1) (if m.Type' = MsgProp then DFrac.own 1 else DFrac.discard) cap st := by
  simp only [h, ↓reduceIte]; exact .rfl

/-- `m.GetSnapshot()` of a message holding no snapshot: `nil`. -/
theorem wp_GetSnapshot_none (Q : raft.Step.ReplPbPostulates (GF := GF) (hG := hG))
    (l : Loc) (dq dqe : DFrac) (cap : Bool) (ms : MsgSt) (h : ms.snap = none) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ msgPtsC l dq dqe cap ms }}
      (App (Val (l @!! go.GoType.PointerType raftpb.Message.ty @!! go!"GetSnapshot")) (Val #()))
    {{ RET #(null : Loc); msgPtsC l dq dqe cap ms }} := by
  iintro %Φ ⟨#Hi, Hm⟩ HΦ
  iapply Q.GetSnapshot.1 l dq dqe cap ms $$ [$Hi $Hm]
  inext
  iintro %ps ⟨Hs, Hback⟩
  ihave Hs' : snapOpt (GF := GF) ps dq none $$ [Hs]
  · rw [← h]; iexact Hs
  simp only [snapOpt]
  icases Hs' with %Hps
  subst Hps
  iapply HΦ
  iapply Hback
  rw [h]; simp only [snapOpt]; ipureintro; trivial

/-- `m.GetEntries()` of a message whose entries are read-only: a read-only entry slice holding
`ms.ents`, the message kept. -/
theorem wp_GetEntries_ro (Q : raft.Step.ReplPbPostulates (GF := GF) (hG := hG))
    (l : Loc) (dq : DFrac) (cap : Bool) (ms : MsgSt) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗
        msgPtsC l dq DFrac.discard cap ms }}
      (App (Val (l @!! go.GoType.PointerType raftpb.Message.ty @!! go!"GetEntries")) (Val #()))
    {{ (es : GoSlice), RET #es; entsRO es ms.ents ∗ msgPtsC l dq DFrac.discard cap ms }} := by
  iintro %Φ ⟨#Hi, Hm⟩ HΦ
  iapply Q.GetEntries.1 l dq DFrac.discard cap ms $$ [$Hi $Hm]
  inext
  iintro %es %els ⟨#Hes, #Hents, Hcap, Hback⟩
  iapply HΦ
  isplitr
  · iunfold entsRO
    iunfold entsPts
    iexists els
    iframe Hes Hents
  iapply Hback $$ %cap %els %ms.ents Hes Hents Hcap

/-- A freshly allocated `&pb.Message{...}` with scalar fields only (`Entries`, `Context`,
`Responses` nil, `Snapshot` nil): an owned message holding `mm` and nothing else. -/
theorem msgOwn_of_scalars (l : Loc) (v : raftpb.Message) (mm : MessageM) (E : CoPset) :
    (⌜v.Entries' = slice.nil ∧ v.Snapshot' = null ∧ v.Context' = slice.nil ∧
       v.Responses' = slice.nil ∧ v.unknownFields' = slice.nil⌝ ∗ l ↦ v ∗ cellRO v.Type' mm.Type' ∗ cellRO v.To' mm.To' ∗
      cellRO v.From' mm.From' ∗ cellRO v.Term' mm.Term' ∗
      cellRO v.LogTerm' mm.LogTerm' ∗ cellRO v.Index' mm.Index' ∗
      cellRO v.Commit' mm.Commit' ∗ cellRO v.Vote' mm.Vote' ∗
      cellRO v.Reject' mm.Reject' ∗ cellRO v.RejectHint' mm.RejectHint' : IProp GF) ⊢
      |={E}=> msgOwn l (DFrac.own 1) ⟨mm, [], none, [], []⟩ := by
  iintro ⟨%Hv, Hl, #cTy, #cTo, #cFr, #cTe, #cLt, #cIx, #cCo, #cVo, #cRj, #cRh⟩
  obtain ⟨Hes, Hsn, Hcx, Hrs, Hu⟩ := Hv
  ihave Hnil : (slice.nil ↦* ([] : List Loc) : IProp GF) $$ []
  · iapply ownSlice_nil
  imod ownSlice_persist $$ Hnil with #Hnil
  ihave Hnilb : (slice.nil ↦* ([] : List w8) : IProp GF) $$ []
  · iapply ownSlice_nil
  imod ownSlice_persist $$ Hnilb with #Hnilb
  ihave Hnilr : (slice.nil ↦* ([] : List Loc) : IProp GF) $$ []
  · iapply ownSlice_nil
  iapply msgOwn_of_struct l v [] _ E Hu
  iframe Hl cTy cTo cFr cTe cLt cIx cCo cVo cRj cRh
  rw [Hes, Hsn, Hcx, Hrs]
  simp only [snapOpt]
  iframe Hnil Hnilb Hnilr
  iapply BigSepL2.bigSepL2_nil.2; itrivial

end StepProof

end base


/-- The getters `wp_get` tries. -/
meta def StepProof.msgGetters : List String :=
  ["GetType", "GetTerm", "GetFrom", "GetTo", "GetIndex", "GetLogTerm", "GetCommit", "GetReject"]

open Lean Elab Tactic in
/-- One read of the message `"Hm"` at the head of the goal, by whichever scalar getter it is,
through `Q : raft.Step.ReplPbPostulates`; then `rw [Hty]` and `wp_auto` where they apply. The
getter is the one the next redex calls (`Dispatch.lean`); where that is not a getter call, each
is tried. -/
elab "wp_get " q:ident : tactic => do
  let alts := match ← StepProof.nextMethod? with
    | some g => if StepProof.msgGetters.contains g then [g] else StepProof.msgGetters
    | none => StepProof.msgGetters
  let alts := alts.map fun g => s!"(wp_apply {q.getId}.{g}.1 $$ [$Hm] as Hm)"
  StepProof.evalTacticString ("first " ++ String.intercalate " " (alts.map ("| " ++ ·)))
  StepProof.evalTacticString "try rw [Hty]"
  StepProof.evalTacticString "try wp_auto"

open Lean Elab Tactic in
/-- `wp_drive`'s search: every alternative in turn, as long as one applies. -/
elab "wp_drive_any " q:ident : tactic => do
  let loads := ["idC", "TermC", "checkQuorumC", "preVoteC", "VoteC", "leadC"].map fun f =>
    s!"(wp_apply raft.wp_load_{f} $$ Hphys as Hphys; try wp_auto)"
  let alts := s!"(wp_get {q.getId})" :: loads ++ ["(rw [Hty]; wp_auto)"]
  StepProof.evalTacticString
    ("repeat (first " ++ String.intercalate " " (alts.map ("| " ++ ·)) ++ ")")

open Lean Elab Tactic in
/-- `Step`'s straight-line reads: the message's scalar getters (`wp_get`), and the raft fields the
preamble and its logging read (`id`, `Term`, `checkQuorum`, `preVote`, `Vote`, `lead`), with
`rw [Hty]; wp_auto` to take the type tests; as long as one applies. Each step is the one the next
redex asks for (`Dispatch.lean`: a getter call, a load of one of the six fields, else the type
test); where that step fails, `wp_drive_any` takes over from there. -/
elab "wp_drive " q:ident : tactic => do
  let loads := [("id", "idC"), ("Term", "TermC"), ("checkQuorum", "checkQuorumC"),
    ("preVote", "preVoteC"), ("Vote", "VoteC"), ("lead", "leadC")]
  let mut fuel := 1000
  while fuel > 0 do
    fuel := fuel - 1
    let step? : Option String ← do
      if let some g ← StepProof.nextMethod? then
        if StepProof.msgGetters.contains g then
          pure (some s!"(wp_apply {q.getId}.{g}.1 $$ [$Hm] as Hm; try rw [Hty]; try wp_auto)")
        else pure none
      else if let some f ← StepProof.nextField? then
        pure ((loads.lookup f).map fun l =>
          s!"(wp_apply raft.wp_load_{l} $$ Hphys as Hphys; try wp_auto)")
      else pure none
    let saved ← saveState
    match step? with
    | some s =>
      try StepProof.evalTacticString s
      catch _ =>
        saved.restore
        StepProof.evalTacticString s!"wp_drive_any {q.getId}"
        return
    | none =>
      try StepProof.evalTacticString "(rw [Hty]; wp_auto)"
      catch _ =>
        saved.restore
        return

set_option hygiene false in
/-- (2026-10-17, `CheckQuorum` on) after `wp_drive` has loaded `r.checkQuorum` in `Step`'s
stale-term arm (`r.checkQuorum || r.preVote`): split on it (`Hcq`) and, where it is off, load
and split on `r.preVote`; each goal driven on (`wp_drive`). -/
macro "cq_split " q:ident : tactic => `(tactic| (
  cases Hcq : s.cq <;> (try wp_auto) <;> (try wp_drive $q)
  all_goals try (
    have _ : s.cq = false := Hcq
    cases Hpv : s.prevote <;> (try wp_auto) <;> wp_drive $q)))

end EtcdGrove
end Perennial
