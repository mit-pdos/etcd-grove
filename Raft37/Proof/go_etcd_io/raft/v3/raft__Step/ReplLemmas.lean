/- The callee specs of raft v3.7's `Step` beyond `raft.Step.Postulates` that the replication,
response, proposal, storage-acknowledgement and read-index branches use (stage R4 phase 3,
group G4b): the `*pb.Message`/`*pb.Entry` getters the body reads the message through, and
`MessageType.Enum` (`&pb.Message{..., Type: pb.MsgAppResp.Enum()}`).

`Base.lean`'s `raft.Step.Postulates` (shared) is unchanged: the branch lemmas take this structure
as a second argument (`_Q`), which the dispatch builds from `raft.Step.wp_proof`'s hypotheses. -/
module

public import Raft37.Proof.go_etcd_io.raft.v3.raft__Step.Base
public import Raft37.Proof.go_etcd_io.raft.v3.InvPbMsg
public import Raft37.Spec.go_etcd_io.raft.v3.raftpb.Message__GetType
public import Raft37.Spec.go_etcd_io.raft.v3.raftpb.Message__GetTerm
public import Raft37.Spec.go_etcd_io.raft.v3.raftpb.Message__GetFrom
public import Raft37.Spec.go_etcd_io.raft.v3.raftpb.Message__GetTo
public import Raft37.Spec.go_etcd_io.raft.v3.raftpb.Message__GetIndex
public import Raft37.Spec.go_etcd_io.raft.v3.raftpb.Message__GetLogTerm
public import Raft37.Spec.go_etcd_io.raft.v3.raftpb.Message__GetCommit
public import Raft37.Spec.go_etcd_io.raft.v3.raftpb.Message__GetReject
public import Raft37.Spec.go_etcd_io.raft.v3.raftpb.Message__GetEntries
public import Raft37.Spec.go_etcd_io.raft.v3.raftpb.Message__GetSnapshot
public import Raft37.Spec.go_etcd_io.raft.v3.raftpb.Message__GetContext
public import Raft37.Spec.go_etcd_io.raft.v3.raftpb.Entry__GetIndex
public import Raft37.Spec.go_etcd_io.raft.v3.raftpb.MessageType__Enum

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section base
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
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

/-- A message's pointer is not `nil` (kept). -/
theorem msgPtsC_not_null (l : Loc) (dq dqe : DFrac) (cap : Bool) (ms : MsgSt) :
    msgPtsC (GF := GF) l dq dqe cap ms ⊢ ⌜l ≠ null⌝ ∗ msgPtsC l dq dqe cap ms := by
  iintro H
  ihave %Hnn : ⌜l ≠ null⌝ $$ [H]
  · iunfold msgPtsC at H
    iNamed H
    ipureintro; exact Hnn
  iframe H
  ipureintro; exact Hnn

/-- The `From` field of a message, lent (`&pb.Message{To: m.From, ...}` reads the pointer: the new
message shares the read-only cell). -/
theorem msgPtsC_From_acc (l : Loc) (dq dqe : DFrac) (cap : Bool) (ms : MsgSt) :
    msgPtsC (GF := GF) l dq dqe cap ms ⊢
      ∃ p : Loc, l.[raftpb.Message, go!"From"] ↦{dq} p ∗ cellRO p ms.msg.From' ∗
        (l.[raftpb.Message, go!"From"] ↦{dq} p -∗ msgPtsC l dq dqe cap ms) := by
  iintro H
  iunfold msgPtsC at H
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

/-- A message `Step` received, off a proposal, as the `stepX` specs take it. -/
theorem msgIn_nonprop {ml : Loc} {m : MessageM} {st : MsgSt} (h : m.Type' ≠ MsgProp) :
    msgIn (GF := GF) ml DFrac.discard st ⊢
      msgIn ml (if m.Type' = MsgProp then DFrac.own 1 else DFrac.discard) st := by
  simp only [h, ↓reduceIte]; exact .rfl

/-- A proposal `Step` received, as the `stepX` specs take it. -/
theorem msgIn_prop {ml : Loc} {m : MessageM} {st : MsgSt} (h : m.Type' = MsgProp) :
    msgIn (GF := GF) ml (DFrac.own 1) st ⊢
      msgIn ml (if m.Type' = MsgProp then DFrac.own 1 else DFrac.discard) st := by
  simp only [h, ↓reduceIte]; exact .rfl

/-- A fresh cell, frozen: read-only. -/
theorem cellRO_of_pointsto {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (p : Loc) (v : V)
    (E : CoPset) : (p ↦ v : IProp GF) ⊢ |={E}=> cellRO p v := by
  iintro H
  imod (typedPointsto_dfractional (GF := GF) _ v).dfractional_persist _ $$ H with #H
  imodintro
  iunfold cellRO
  iright
  iexact H

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


open Lean Elab Tactic in
/-- Run the tactic text `s`, parsed at the call site (so its names, `Hm`, `Hphys`, `Hty`, are
the caller's hypotheses). -/
meta def StepProof.evalTacticString (s : String) : TacticM Unit := do
  match Parser.runParserCategory (← getEnv) `tactic s with
  | .ok stx => evalTactic stx
  | .error e => throwError "evalTacticString: {e}"

/-- The getters `wp_get` tries. -/
meta def StepProof.msgGetters : List String :=
  ["GetType", "GetTerm", "GetFrom", "GetTo", "GetIndex", "GetLogTerm", "GetCommit", "GetReject"]

open Lean Elab Tactic in
/-- One read of the message `"Hm"` at the head of the goal, by whichever scalar getter it is,
through `Q : raft.Step.ReplPbPostulates`; then `rw [Hty]` and `wp_auto` where they apply. -/
elab "wp_get " q:ident : tactic => do
  let alts := StepProof.msgGetters.map fun g =>
    s!"(wp_apply {q.getId}.{g}.1 $$ [$Hm] as Hm)"
  StepProof.evalTacticString ("first " ++ String.intercalate " " (alts.map ("| " ++ ·)))
  StepProof.evalTacticString "try rw [Hty]"
  StepProof.evalTacticString "try wp_auto"

open Lean Elab Tactic in
/-- `Step`'s straight-line reads: the message's scalar getters (`wp_get`), and the raft fields the
preamble and its logging read (`id`, `Term`, `checkQuorum`, `preVote`, `Vote`, `lead`), with
`rw [Hty]; wp_auto` to take the type tests; as long as one applies. -/
elab "wp_drive " q:ident : tactic => do
  let loads := ["idC", "TermC", "checkQuorumC", "preVoteC", "VoteC", "leadC"].map fun f =>
    s!"(wp_apply raft.wp_load_{f} $$ Hphys as Hphys; try wp_auto)"
  let alts := s!"(wp_get {q.getId})" :: loads ++ ["(rw [Hty]; wp_auto)"]
  StepProof.evalTacticString
    ("repeat (first " ++ String.intercalate " " (alts.map ("| " ++ ·)) ++ ")")

end EtcdGrove
end Perennial
