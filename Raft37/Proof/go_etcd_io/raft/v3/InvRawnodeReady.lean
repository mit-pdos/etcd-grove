/-
**Raft v3.7 (2026-10-16, stage R5 of the retarget, `notes/decisions.md`, "The node layer over
pointer messages", D8).** Ported from the old proof's file. What changed: `readyWithoutAccept`
**hands the messages out** (D8): `rd.Messages` (a `[]*pb.Message` aliasing `r.msgs`, extended by
the `msgsAfterAppend` messages to others) with the messages' ownership, so `ownRaftPhysReady`
keeps the queues' slices and the *pure* outbox relation (`outboxRelP`), the self-addressed
`msgsAfterAppend` messages owned (`selfOwn`, which `acceptReady` moves to `stepsOnAdvance`), and
**half** of the messages to others (`otherHalf`): `acceptReady` runs after `node.go` sent the
`Ready` and reads `m.GetTo()` of every `msgsAfterAppend` message, so the application gets those
responses at half (`readyDq`, by type: every `MsgAppResp`/`MsgVoteResp`/`MsgPreVoteResp`
handed out goes at half, the other half kept -- `msgsAfterAppend`'s in `otherHalf`, `r.msgs`'s
inside `Hundo`), every other message whole. `Hundo` takes the handed-out messages back and gives
`r.msgs`' slice, its messages and the others' halves (the way back, `ownRawNodeReady_abandon`).
The handed-out messages are `ms : List QMsg` (pointer and state: the way back needs the
pointers). `Ready`'s fields: `HardState` a `hsOpt` (`nil` or `hardState()`'s fresh one),
`Snapshot` `nil`, `ReadStates` `readStatesPts`, `Entries`/`CommittedEntries` `entsRO` (the
latter's capacity owned, for the queued `MsgStorageApplyResp`). A read state's context is its
bytes (D6), so `readStateOk_readOk` takes the bytes' equality (no `isPropData`).

**A `Ready` computed but not yet accepted (2026-10-10)**

`node.go`'s `run` does not call `RawNode.Ready`: it calls its two halves,
`readyWithoutAccept` (when `HasReady`), hands the `Ready` to the application
(`readyc <- rd`), and only then `acceptReady(rd)`, with no raft step in between.
`ownRawNodeReady γ rn id rs rd ce es` is the node between the two: `ownRawNode γ rn id rs`
with the outbox `r.msgs`' slice given up to `rd.Messages` (`readyWithoutAccept` builds
`rd.Messages` in place from `r.msgs`, and `acceptReady` only sets the field to `nil`), and
what `acceptReady` reads of `rd` recorded: the soft state pointer read-only (or `nil`), no
snapshot, the read states (2026-10-13: below), the committed entries `ce` (read-only, with the slice's capacity,
which `acceptReady` hands to the queued `MsgStorageApplyResp`) and the entries `es` handed
out for the storage. The node itself is as `readyWithoutAccept` found it (it only reads);
`acceptReady` takes the predicate back to `ownRawNode` at the post-`Ready` state.

`ownRaftPhysReady` is `ownRaftPhys` opened as `ownRaftPhys_view` opens it, without the
contents of `r.msgs`' slice (the field is kept): what `acceptReady` needs to close it with
empty queues.

**Abandoning a `Ready` (2026-10-10).** `node.go` recomputes `rd` when its `select` takes
another case, and steps the node meanwhile: the computed `Ready` is dropped, and the node
must be whole again. `ownRawNodeReady_abandon` gives it back, `ownRawNode γ rn id rs`, for
the messages handed out (`rd.Messages ↦* ms` with its capacity). The messages are built by
appending onto `r.msgs`, which Go may do in place (into `r.msgs`' capacity) or by copying
into a new array (leaving the old one untouched); either way `r.msgs`' slice and capacity
can be recovered from the new ones (Perennial's `wp_slice_append_undo`). So
`ownRaftPhysReady` keeps a wand `Hundo` from `rd.Messages`' contents and capacity back to
`r.msgs`' (indexed by the slice and the list it was built for, `ms`, a parameter of
`ownRawNodeReady`), and the queues' term bound (`OutTermOk`) for the wand `Hclose`.

**Read states (2026-10-13).** `readyWithoutAccept` sets `rd.ReadStates = r.readStates`
when it is not empty, and `acceptReady` sets `r.readStates = nil` when `rd.ReadStates` is
not empty. The slice is read-only in the struct (`ownRaftMisc`), so `readyWithoutAccept`
hands out `rd.ReadStates ↦*□ sts` and each `ReadState`'s `readStateOk`, persistent facts
it copies out of the ghost state (`ownRaftGhost_readStates`) without a model step: nothing
has to be given back when the `Ready` is abandoned, and a stale `Ready` that `node.go`
sends later still carries them. `acceptReady` takes the model step `Step.takeReads`
(the protocol state's `ReadState`s become `[]`, as the struct's do); what it needs of `rd`
is that an empty `rd.ReadStates` means the node has no `ReadState` (`Hrdrs`): true of a
fresh `Ready` (the slice is the node's when non-empty) and of an idle node (`HasReady`
is `false` only when `r.readStates` is empty, `ownRawNodeIdle`).

**Read credits (2026-10-13).** Each `MsgReadIndex` in the abstract outbox carries a read
credit (`ownRaftGhost`'s `rdOwn`), and `Ready` hands each one out with its message, for the
transport to pass to the receiver's `Step`. The credits come out of the ghost state with
the drain of the abstract outbox (`ownRaftGhost_drain`), which `ownRawNodeReady_handout`
takes -- where the `Ready` is handed out (`node.go`: in the atomic update of `readyc <- rd`)
-- rather than `acceptReady`: `ownRawNodeReady … true`'s ghost state is at the drained
outbox, while the struct's queues are emptied only by `acceptReady`. So
`ownRawNodeReady` records, of the outbox `readyWithoutAccept` found, that its messages were
legitimately sent (`Hout`, which `acceptReady` needs of the self-addressed responses it
queues) and that the messages handed out hold at most as many `MsgReadIndex`s as it had
credits for (`Hrdc`: `rdCountM ms ≤ rdCount ps.outbox`, from `outboxRel`: a physical
message is a `MsgReadIndex` iff its abstraction is a `readIndex`, `msgAbs_rdCount`).
-/
module

public import Raft37.Proof.go_etcd_io.raft.v3.InvRawnode
-- `ownRaftGhost_drain` (2026-10-13)
public import Raft37.Proof.go_etcd_io.raft.v3.Protocol.Refinement

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

set_option hygiene false in
/-- Combine two fractions of a field points-to at one value (`icombine` gives the agreement). -/
local macro "pcomb " h:ident h':ident : tactic =>
  `(tactic| (icombine $h:ident $h':ident gives %e; subst e
             icombine $h:ident $h':ident as $h:ident
             ihave $h:ident := ((typedPointsto_dfractional (GF := GF) _ _).dfractional _ _).2 $$ $h:ident))

set_option hygiene false in
/-- Combine two fractions of a slice points-to at one list. -/
local macro "scomb " h:ident h':ident : tactic =>
  `(tactic| (icombine $h:ident $h':ident as $h:ident
             ihave $h:ident := ((ownSlice_dfractional (GF := GF) _ _).dfractional _ _).2 $$ $h:ident))

/-! ## Fractions of a message combine (2026-10-16, stage R5)

The converses of `InvPb.lean`'s `*_split` lemmas, for the halves of the responses a `Ready`
hands out (`ownRaftPhysReady`, the way back). -/

section combine
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

-- Named apart from `LemmasSendRD.csPts_combine` (which keeps the first `AutoLeave`): both reach `Link.lean`.
theorem csPts_combine_open (p : Loc) (dq1 dq2 : DFrac) (c : ConfStateM) (al1 al2 : Bool) :
    csPts (GF := GF) p dq1 c al1 ∗ csPts p dq2 c al2 ⊢ csPts p (dq1 • dq2) c false := by
  iintro ⟨H1, H2⟩
  iunfold csPts at H1 H2
  icases H1 with ⟨%sv, %sl, %so, %sn, %pa, %Hnn, HV, Hv, HL, Hl, HO, Ho, HN, Hn, HA, #cA, %-, #Hpb⟩
  icases H2 with ⟨%sv', %sl', %so', %sn', %pa', %-, HV', Hv', HL', Hl', HO', Ho', HN', Hn', HA', -, %-, -⟩
  pcomb HV HV'
  pcomb HL HL'
  pcomb HO HO'
  pcomb HN HN'
  pcomb HA HA'
  scomb Hv Hv'
  scomb Hl Hl'
  scomb Ho Ho'
  scomb Hn Hn'
  iunfold csPts
  iexists sv, sl, so, sn, pa
  isplitr
  · ipureintro; exact Hnn
  simp only [named]
  iframe HV Hv HL Hl HO Ho HN Hn HA cA Hpb
  ipureintro; intro h; cases h

theorem csOptA_combine (p : Loc) (dq1 dq2 : DFrac) (c : ConfStateM) :
    csOptA (GF := GF) p dq1 c ∗ csOptA p dq2 c ⊢ csOptA p (dq1 • dq2) c := by
  iintro ⟨H1, H2⟩
  iunfold csOptA at H1 H2
  icases H1 with (%H1 | H1 | H1) <;> icases H2 with (%H2 | H2 | H2)
  all_goals first
    | (iunfold csOptA; ileft; ipureintro; exact H1)
    | (icases csPts_nn _ _ _ _ $$ H2 with ⟨-, %Hn⟩; exact absurd H1.1 Hn)
    | (icases csPts_nn _ _ _ _ $$ H1 with ⟨-, %Hn⟩; exact absurd H2.1 Hn)
    | (iunfold csOptA; iright; iright; iexact H2)
    | (iunfold csOptA; iright; iright; iexact H1)
    | (iunfold csOptA; iright; ileft; iapply csPts_combine_open p dq1 dq2 c false false; isplitl [H1]
       · iexact H1
       · iexact H2)

theorem smPts_combine (p : Loc) (dq1 dq2 : DFrac) (md : SnapshotMetadataM) :
    smPts (GF := GF) p dq1 md ∗ smPts p dq2 md ⊢ smPts p (dq1 • dq2) md := by
  iintro ⟨H1, H2⟩
  iunfold smPts at H1 H2
  icases H1 with ⟨%pc, %pi, %pt, %uf, %Hnn, HC, Hc, HI, #cI, HT, #cT, #Hpb⟩
  icases H2 with ⟨%pc', %pi', %pt', %uf', %-, HC', Hc', HI', -, HT', -, -⟩
  pcomb HC HC'
  pcomb HI HI'
  pcomb HT HT'
  ihave Hc := csOptA_combine _ _ _ _ $$ [Hc Hc']
  · iframe Hc Hc'
  iunfold smPts
  iexists pc, pi, pt, uf
  isplitr
  · ipureintro; exact Hnn
  simp only [named]
  iframe HC Hc HI cI HT cT Hpb

theorem smOpt_combine (p : Loc) (dq1 dq2 : DFrac) (md : SnapshotMetadataM) :
    smOpt (GF := GF) p dq1 md ∗ smOpt p dq2 md ⊢ smOpt p (dq1 • dq2) md := by
  iintro ⟨H1, H2⟩
  iunfold smOpt at H1 H2
  icases H1 with (%H1 | H1) <;> icases H2 with (%H2 | H2)
  · iunfold smOpt; ileft; ipureintro; exact H1
  · iunfold smPts at H2; icases H2 with ⟨%_, %_, %_, %_, %Hn, -⟩; exact absurd H1.1 Hn
  · iunfold smPts at H1; icases H1 with ⟨%_, %_, %_, %_, %Hn, -⟩; exact absurd H2.1 Hn
  · iunfold smOpt; iright; iapply smPts_combine; iframe H1 H2

theorem ownSnapM_combine (p : Loc) (dq1 dq2 : DFrac) (sn : SnapshotM) :
    ownSnapM (GF := GF) p dq1 sn ∗ ownSnapM p dq2 sn ⊢ ownSnapM p (dq1 • dq2) sn := by
  iintro ⟨H1, H2⟩
  iunfold ownSnapM at H1 H2
  icases H1 with ⟨%ds, %pm, %uf, %Hnn, HD, Hd, HM, Hm, #Hpb⟩
  icases H2 with ⟨%ds', %pm', %uf', %-, HD', Hd', HM', Hm', -⟩
  pcomb HD HD'
  pcomb HM HM'
  scomb Hd Hd'
  ihave Hm := smOpt_combine _ _ _ _ $$ [Hm Hm']
  · iframe Hm Hm'
  iunfold ownSnapM
  iexists ds, pm, uf
  isplitr
  · ipureintro; exact Hnn
  simp only [named]
  iframe HD Hd HM Hm Hpb

theorem snapOpt_combine (p : Loc) (dq1 dq2 : DFrac) (o : Option SnapshotM) :
    snapOpt (GF := GF) p dq1 o ∗ snapOpt p dq2 o ⊢ snapOpt p (dq1 • dq2) o := by
  rcases o with _ | sn
  · simp only [snapOpt]
    iintro ⟨%H, -⟩
    ipureintro; exact H
  · simp only [snapOpt]
    iapply ownSnapM_combine

/-- Two fractions of a message at one state combine (2026-10-16, stage R5: the halves of a
response a `Ready` hands out, `InvRawnodeReady.lean`). -/
theorem msgOwn_combine (l : Loc) (dq1 dq2 : DFrac) (ms : MsgSt) :
    msgOwn (GF := GF) l dq1 ms ∗ msgOwn l dq2 ms ⊢ msgOwn l (dq1 • dq2) ms := by
  iintro ⟨H1, H2⟩
  simp only [msgOwn, msgPts]
  iunfold msgPtsC at H1 H2
  icases H1 with ⟨%pty, %pto, %pfr, %pte, %plt, %pix, %pco, %pvo, %prj, %prh, %es, %els, %ps, %cs,
    %rs, %uf, %Hnn, HTy, #cTy, HTo, #cTo, HFr, #cFr, HTe, #cTe, HLt, #cLt, HIx, #cIx, HCo, #cCo,
    HVo, #cVo, HRj, #cRj, HRh, #cRh, HEs, #Hes, #Hents, -, HSn, Hsn, HCx, #Hcs, HRs, Hrs, #Hpb⟩
  icases H2 with ⟨%pty', %pto', %pfr', %pte', %plt', %pix', %pco', %pvo', %prj', %prh', %es',
    %els', %ps', %cs', %rs', %uf', %-, HTy', -, HTo', -, HFr', -, HTe', -, HLt', -, HIx', -, HCo', -,
    HVo', -, HRj', -, HRh', -, HEs', #Hes', -, -, HSn', Hsn', HCx', -, HRs', Hrs', -⟩
  pcomb HTy HTy'
  pcomb HTo HTo'
  pcomb HFr HFr'
  pcomb HTe HTe'
  pcomb HLt HLt'
  pcomb HIx HIx'
  pcomb HCo HCo'
  pcomb HVo HVo'
  pcomb HRj HRj'
  pcomb HRh HRh'
  pcomb HEs HEs'
  pcomb HSn HSn'
  pcomb HCx HCx'
  pcomb HRs HRs'
  scomb Hrs Hrs'
  ihave Hsn := snapOpt_combine _ _ _ _ $$ [Hsn Hsn']
  · iframe Hsn Hsn'
  iunfold msgPtsC
  iexists pty, pto, pfr, pte, plt, pix, pco, pvo, prj, prh, es, els, ps, cs, rs, uf
  isplitr
  · ipureintro; exact Hnn
  simp only [named, Bool.false_eq_true, ↓reduceIte]
  iframe HTy cTy HTo cTo HFr cFr HTe cTe HLt cLt HIx cIx HCo cCo HVo cVo HRj cRj HRh cRh HEs
    Hes Hents HSn Hsn HCx Hcs HRs Hrs Hpb

end combine

section pure
variable [FfiSyntax]

/-- What `acceptReady` needs of the committed entries `ce` a `Ready` hands out
(2026-10-10): they are the next ones after `applying`, up to at most `committed` -- its
`acceptApplying` moves `applying` to the last one's index, and the queued
`MsgStorageApplyResp` acknowledges them. Until 2026-10-10 `ownRawNodeReady` recorded
`ce <+: logCommittedEnts s.logst`, which implies this (`ceOk_of_prefix`); this weaker fact
survives the steps `node.go` takes after abandoning a `Ready` (they keep `applying` and do
not lower `committed`), so that an abandoned `Ready` can still be accepted
(`ownRawNodeIdle_ready`). -/
def CeOk (ls : LogState) (ce : List EntryM) : Prop :=
  ∀ e, ce.getLast? = some e →
    uint.Z ls.applying < uint.Z e.Index' ∧ uint.Z e.Index' ≤ uint.Z ls.committed ∧
    uint.Z e.Index' = uint.Z ls.applying + (ce.length : Int)

theorem ceOk_of_prefix (ls : LogState) (ce : List EntryM)
    (Hidx : LogIndicesOk ls.prev (ls.sents ++ ls.uents))
    (Hle : uint.Z ls.prev.index' ≤ uint.Z ls.applying ∧ uint.Z ls.applying ≤ uint.Z ls.committed)
    (Hnw : uint.Z ls.committed + 1 < 2 ^ 64)
    (Hce : ce <+: logCommittedEnts ls) : CeOk ls ce := by
  intro e Hl
  unfold logCommittedEnts plogFrom at Hce
  have Hk : (uint.Z (ls.applying + W64 1) - uint.Z ls.prev.index' - 1).toNat
      = (uint.Z ls.applying - uint.Z ls.prev.index').toNat := by word
  rw [Hk] at Hce
  obtain ⟨ce0, rfl⟩ := List.getLast?_eq_some_iff.1 Hl
  have Hlen := Hce.length_le
  simp only [List.length_append, List.length_singleton, List.length_take] at Hlen
  have Hlk : (ce0 ++ [e])[ce0.length]? = some e := by simp
  have H1 := prefix_getElem? Hce Hlk
  rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop] at H1
  have H2 := Hidx _ _ H1
  push_cast at H2
  simp only [List.length_append, List.length_singleton]
  omega

/-! ### The outbox, pure (2026-10-16, stage R5)

`outboxRel` (`InvRaftPhys.lean`) owns the queued messages; `outboxRelP` is what it says of their
states, which `ownRaftPhysReady` keeps once the messages are handed out. -/

/-- The pure part of `outboxRel`: the outbox `o` is, up to permutation, what the two queues'
messages contribute (`msgAbs`). -/
def outboxRelP (o : List Msg) (ms1 ms2 : List QMsg) : Prop :=
  ∃ (as1 as2 : List (Option Msg)), o ≡ₚ absList as1 ++ absList as2 ∧
    List.Forall₂ (fun q a => msgAbs q.st a) ms1 as1 ∧ List.Forall₂ (fun q a => msgAbs q.st a) ms2 as2

/-- A response type: what `send` queues in `msgsAfterAppend` (`AAMsgOk`). -/
def RespType (t : w32) : Prop := t = MsgAppResp ∨ t = MsgVoteResp ∨ t = MsgPreVoteResp

instance (t : w32) : Decidable (RespType t) := by unfold RespType; infer_instance

/-- The fraction at which a `Ready` hands a message out (see the file header): half of a
response (`acceptReady` reads the other half's `To`), the whole of any other. -/
def readyDq (st : MsgSt) : DFrac :=
  if RespType st.msg.Type' then DFrac.own (1 : Qp).half else DFrac.own 1

/-- `msgsAfterAppend`'s messages to the node itself, which `acceptReady` queues. -/
def isSelfQ (id : w64) (q : QMsg) : Bool := decide (q.st.msg.To' = id)

end pure

section rawnodeReady
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- A queued message's ownership. -/
abbrev qOwn (q : QMsg) : IProp GF := msgOwn q.loc (DFrac.own 1) q.st

/-- A self-addressed `msgsAfterAppend` message, owned (`emp` for any other). -/
def selfOwn (id : w64) (q : QMsg) : IProp GF :=
  if isSelfQ id q then qOwn q else iprop(emp)

/-- Half of a `msgsAfterAppend` message to another node (`emp` for a self-addressed one):
what the node keeps of the responses a `Ready` hands out. -/
def otherHalf (id : w64) (q : QMsg) : IProp GF :=
  if isSelfQ id q then iprop(emp) else msgOwn q.loc (DFrac.own (1 : Qp).half) q.st

/-- Half of a response (`emp` for any other message): what is kept of a message handed out at
`readyDq`. -/
def respHalf (q : QMsg) : IProp GF :=
  if RespType q.st.msg.Type' then msgOwn q.loc (DFrac.own (1 : Qp).half) q.st else iprop(emp)

theorem dfrac_half_half : (DFrac.own (1 : Qp).half • DFrac.own (1 : Qp).half : DFrac) = DFrac.own 1 := by
  rw [DFrac.op_own, Qp.half_add_half]

/-- A message handed out: at `readyDq`, the other half (`respHalf`) kept. -/
theorem qOwn_ready (q : QMsg) :
    qOwn (GF := GF) q ⊢ msgOwn q.loc (readyDq q.st) q.st ∗ respHalf q := by
  iintro H
  unfold readyDq respHalf
  by_cases h : RespType q.st.msg.Type'
  · simp only [h, ↓reduceIte]
    iapply (msgOwn_split q.loc (DFrac.own (1 : Qp).half) (DFrac.own (1 : Qp).half) q.st)
    rw [dfrac_half_half]
    iexact H
  · simp only [h, ↓reduceIte]
    iframe H

/-- ... and back. -/
theorem qOwn_unready (q : QMsg) :
    msgOwn (GF := GF) q.loc (readyDq q.st) q.st ∗ respHalf q ⊢ qOwn q := by
  iintro ⟨H1, H2⟩
  unfold readyDq respHalf
  by_cases h : RespType q.st.msg.Type'
  · simp only [h, ↓reduceIte]
    unfold qOwn
    rw [← dfrac_half_half]
    iapply msgOwn_combine
    iframe H1 H2
  · simp only [h, ↓reduceIte]
    iexact H1

/-- Owning a queue's messages is owning the self-addressed ones and the others (2026-10-16). -/
theorem qOwns_self_split (id : w64) (l : List QMsg) :
    ([∗list] q ∈ l, qOwn (GF := GF) q) ⊣⊢
      ([∗list] q ∈ l, selfOwn id q) ∗ [∗list] q ∈ l.filter (fun q => !isSelfQ id q), qOwn q := by
  induction l with
  | nil => simp only [List.filter_nil]; exact ⟨by iintro -; isplitl <;> iempintro, by iintro -; iempintro⟩
  | cons q l ih =>
    by_cases h : isSelfQ id q = true
    · simp only [List.filter_cons, h, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      constructor
      · iintro H
        icases BigSepL.bigSepL_cons.1 $$ H with ⟨Hq, H⟩
        icases ih.1 $$ H with ⟨H1, H2⟩
        iframe H2
        iapply BigSepL.bigSepL_cons.2
        iframe H1
        unfold selfOwn; simp only [h, ↓reduceIte]; iexact Hq
      · iintro ⟨H1, H2⟩
        icases BigSepL.bigSepL_cons.1 $$ H1 with ⟨Hq, H1⟩
        iapply BigSepL.bigSepL_cons.2
        isplitl [Hq]
        · unfold selfOwn; simp only [h, ↓reduceIte]; iexact Hq
        iapply ih.2; iframe H1 H2
    · simp only [List.filter_cons, h, Bool.not_false, ↓reduceIte]
      constructor
      · iintro H
        icases BigSepL.bigSepL_cons.1 $$ H with ⟨Hq, H⟩
        icases ih.1 $$ H with ⟨H1, H2⟩
        isplitl [H1]
        · iapply BigSepL.bigSepL_cons.2
          iframe H1
          unfold selfOwn; simp only [h, Bool.false_eq_true, ↓reduceIte]; iempintro
        iapply BigSepL.bigSepL_cons.2
        iframe Hq H2
      · iintro ⟨H1, H2⟩
        icases BigSepL.bigSepL_cons.1 $$ H1 with ⟨-, H1⟩
        icases BigSepL.bigSepL_cons.1 $$ H2 with ⟨Hq, H2⟩
        iapply BigSepL.bigSepL_cons.2
        iframe Hq
        iapply ih.2; iframe H1 H2

/-- The messages to others, owned, are their halves twice. -/
theorem qOwns_other_halves (id : w64) (l : List QMsg) :
    ([∗list] q ∈ l.filter (fun q => !isSelfQ id q), msgOwn (GF := GF) q.loc (DFrac.own (1 : Qp).half) q.st) ∗
      ([∗list] q ∈ l, otherHalf id q) ⊣⊢
      [∗list] q ∈ l.filter (fun q => !isSelfQ id q), qOwn q := by
  induction l with
  | nil => simp only [List.filter_nil]; exact ⟨by iintro -; iempintro, by iintro -; isplitl <;> iempintro⟩
  | cons q l ih =>
    by_cases h : isSelfQ id q = true
    · simp only [List.filter_cons, h, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      constructor
      · iintro ⟨H1, H2⟩
        icases BigSepL.bigSepL_cons.1 $$ H2 with ⟨-, H2⟩
        iapply ih.1; iframe H1 H2
      · iintro H
        icases ih.2 $$ H with ⟨H1, H2⟩
        iframe H1
        iapply BigSepL.bigSepL_cons.2
        iframe H2
        unfold otherHalf; simp only [h, ↓reduceIte]; iempintro
    · simp only [List.filter_cons, h, Bool.not_false, ↓reduceIte]
      have e := dfrac_half_half
      constructor
      · iintro ⟨H1, H2⟩
        icases BigSepL.bigSepL_cons.1 $$ H1 with ⟨Hq1, H1⟩
        icases BigSepL.bigSepL_cons.1 $$ H2 with ⟨Hq2, H2⟩
        iapply BigSepL.bigSepL_cons.2
        isplitl [Hq1 Hq2]
        · unfold otherHalf; simp only [h, Bool.false_eq_true, ↓reduceIte]
          unfold qOwn
          rw [← e]
          iapply msgOwn_combine
          iframe Hq1 Hq2
        iapply ih.1; iframe H1 H2
      · iintro H
        icases BigSepL.bigSepL_cons.1 $$ H with ⟨Hq, H⟩
        icases ih.2 $$ H with ⟨H1, H2⟩
        ihave Hq : msgOwn q.loc (DFrac.own (1 : Qp).half • DFrac.own (1 : Qp).half) q.st $$ [Hq]
        · rw [e]; iexact Hq
        icases msgOwn_split q.loc _ _ q.st $$ Hq with ⟨Hq1, Hq2⟩
        isplitl [Hq1 H1]
        · iapply BigSepL.bigSepL_cons.2; iframe Hq1 H1
        iapply BigSepL.bigSepL_cons.2
        iframe H2
        unfold otherHalf; simp only [h, Bool.false_eq_true, ↓reduceIte]; iexact Hq2

/-- `msgQ`s are the messages owned and their contributions. -/
theorem msgQs_split (l : List QMsg) (as_ : List (Option Msg)) :
    ([∗list] _k ↦ q;a ∈ l;as_, msgQ (GF := GF) q a) ⊣⊢
      ⌜List.Forall₂ (fun q a => msgAbs q.st a) l as_⌝ ∗ [∗list] q ∈ l, qOwn q := by
  induction l generalizing as_ with
  | nil =>
    cases as_ with
    | nil =>
      constructor
      · iintro -; isplitr
        · ipureintro; exact List.Forall₂.nil
        · iempintro
      · iintro -; iapply (BigSepL2.bigSepL2_nil (Φ := fun _ q a => msgQ (GF := GF) q a)).2; iempintro
    | cons a as' =>
      constructor
      · iintro H; ihave %Hl := BigSepL2.bigSepL2_length $$ H; simp at Hl
      · iintro ⟨%H, -⟩; cases H
  | cons q l ih =>
    cases as_ with
    | nil =>
      constructor
      · iintro H; ihave %Hl := BigSepL2.bigSepL2_length $$ H; simp at Hl
      · iintro ⟨%H, -⟩; cases H
    | cons a as' =>
      constructor
      · iintro H
        icases (BigSepL2.bigSepL2_cons (Φ := fun _ q a => msgQ (GF := GF) q a)).1 $$ H with ⟨Hq, H⟩
        icases (ih as').1 $$ H with ⟨%Hf, H⟩
        unfold msgQ
        icases Hq with ⟨Hq, %Ha⟩
        isplitr
        · ipureintro; exact List.Forall₂.cons Ha Hf
        iapply BigSepL.bigSepL_cons.2; iframe Hq H
      · iintro ⟨%Hf, H⟩
        icases BigSepL.bigSepL_cons.1 $$ H with ⟨Hq, H⟩
        cases Hf with
        | cons Ha Hf =>
          iapply (BigSepL2.bigSepL2_cons (Φ := fun _ q a => msgQ (GF := GF) q a)).2
          isplitl [Hq]
          · unfold msgQ; iframe Hq; ipureintro; exact Ha
          iapply (ih as').2
          isplitr
          · ipureintro; exact Hf
          iexact H

/-- `outboxRel` is its pure part and the messages owned (2026-10-16, stage R5). -/
theorem outboxRel_split (o : List Msg) (ms1 ms2 : List QMsg) :
    outboxRel (GF := GF) o ms1 ms2 ⊢
      ⌜outboxRelP o ms1 ms2⌝ ∗ ([∗list] q ∈ ms1, qOwn q) ∗ [∗list] q ∈ ms2, qOwn q := by
  iintro H
  unfold outboxRel
  icases H with ⟨%as1, %as2, %Ho, H1, H2⟩
  icases (msgQs_split ms1 as1).1 $$ H1 with ⟨%Hf1, H1⟩
  icases (msgQs_split ms2 as2).1 $$ H2 with ⟨%Hf2, H2⟩
  iframe H1 H2
  ipureintro; exact ⟨as1, as2, Ho, Hf1, Hf2⟩

theorem outboxRel_join (o : List Msg) (ms1 ms2 : List QMsg) :
    ⌜outboxRelP o ms1 ms2⌝ ∗ ([∗list] q ∈ ms1, qOwn (GF := GF) q) ∗ ([∗list] q ∈ ms2, qOwn q) ⊢
      outboxRel o ms1 ms2 := by
  iintro ⟨%Hp, H1, H2⟩
  obtain ⟨as1, as2, Ho, Hf1, Hf2⟩ := Hp
  unfold outboxRel
  iexists as1, as2
  isplitr
  · ipureintro; exact Ho
  isplitl [H1]
  · iapply (msgQs_split ms1 as1).2; iframe H1; ipureintro; exact Hf1
  · iapply (msgQs_split ms2 as2).2; iframe H2; ipureintro; exact Hf2

/-- A queued message's contribution is in the outbox, so it was legitimately sent
(`isRaftMsg`, 2026-10-16): what `readyWithoutAccept` says of the messages it hands out, and
`acceptReady` of the self-addressed responses it queues. -/
theorem outboxRelP_isRaftMsg (γ : RaftNames) (o : List Msg) (ms1 ms2 : List QMsg) (q : QMsg)
    (Hp : outboxRelP o ms1 ms2) (Hq : q ∈ ms1 ++ ms2) :
    ([∗list] x ∈ o, isMessage (GF := GF) γ x) ⊢ isRaftMsg γ q.st := by
  obtain ⟨as1, as2, Ho, Hf1, Hf2⟩ := Hp
  have Hex : ∃ a, msgAbs q.st a ∧ ∀ x ∈ a.toList, x ∈ o := by
    have hsub : ∀ (l : List QMsg) (as_ : List (Option Msg)),
        List.Forall₂ (fun q a => msgAbs q.st a) l as_ → q ∈ l →
        ∃ a, msgAbs q.st a ∧ ∀ x ∈ a.toList, x ∈ absList as_ := by
      intro l as_ hf hm
      induction hf with
      | nil => cases hm
      | @cons q' a' l' as' ha hf ih =>
        rcases List.mem_cons.1 hm with rfl | hm
        · refine ⟨a', ha, fun x hx => ?_⟩
          cases a' with
          | none => cases hx
          | some y =>
            simp only [Option.toList_some, List.mem_singleton] at hx
            subst hx; simp [absList]
        · obtain ⟨a, h1, h2⟩ := ih hm
          refine ⟨a, h1, fun x hx => ?_⟩
          have := h2 x hx
          cases a' <;> simp_all [absList]
    rcases List.mem_append.1 Hq with hm | hm
    · obtain ⟨a, h1, h2⟩ := hsub ms1 as1 Hf1 hm
      exact ⟨a, h1, fun x hx => Ho.symm.subset (List.mem_append_left _ (h2 x hx))⟩
    · obtain ⟨a, h1, h2⟩ := hsub ms2 as2 Hf2 hm
      exact ⟨a, h1, fun x hx => Ho.symm.subset (List.mem_append_right _ (h2 x hx))⟩
  obtain ⟨a, Ha, Hin⟩ := Hex
  iintro #Ho
  unfold isRaftMsg
  iexists a
  isplitr
  · ipureintro; exact Ha
  cases a with
  | none => simp only [Option.toList_none]; iapply BigSepL.bigSepL_nil.2; iempintro
  | some x =>
    simp only [Option.toList_some]
    iapply BigSepL.bigSepL_singleton.2
    iapply (BigSepL.bigSepL_mem (Φ := fun x => isMessage (GF := GF) γ x)
      (Hin x (by simp))) $$ Ho

/-- The abstraction of a message `isRaftMsg` covers, for a type the model describes but a
snapshot (2026-10-16): what `raft.Step`'s `Hmsg` asks of it. -/
theorem isRaftMsg_isMessage (γ : RaftNames) (st : MsgSt) (ty : MsgType)
    (Hty : mtypeOf st.msg.Type' = some ty) (Hns : ty ≠ .snap) :
    isRaftMsg (GF := GF) γ st ⊢ isMessage γ (absMsg ty st.msg st.ents st.ctx) := by
  iintro #H
  unfold isRaftMsg
  icases H with ⟨%a, %Ha, #H⟩
  rcases Ha with ⟨Hn, -⟩ | ⟨ty', Hty', -, rfl⟩ | ⟨sv, Hs, -, -⟩
  · rw [Hty] at Hn; cases Hn
  · rw [Hty] at Hty'; cases Hty'
    simp only [Option.toList_some]
    iapply BigSepL.bigSepL_singleton.1 $$ H
  · rw [Hty] at Hs; cases Hs; exact absurd rfl Hns

/-- The raft struct at `s`, open as `ownRaftPhysC_view` opens it, with the messages of the
outbox handed out (to a `Ready`'s `Messages`, the slice `msl` holding the pointers of `ms`), and
the way back (`Hundo`): see the file header. Since 2026-10-10 also the ghost lower bounds
(`NGhost`, `Hgh_out`, `Hgh_unst`), and that the messages handed out are at most those queued
(`Hmslen`), which the wand `Hclose` lets raise (`ownRawNodeReady_abandon`). (2026-10-16, stage R5:
D8, the messages handed out; the queues `List QMsg`; the outbox relation pure (`Houtbox`,
`outboxRelP`) with the self-addressed `msgsAfterAppend` messages owned (`Hself`) and half of the
others (`Hother`); `Hundo` takes the handed-out messages back (at `readyDq`) and gives `r.msgs`'
slice and messages and the others' halves; the read states `readStatesPts`; `Hclose` as
`ownRaftPhysC_view`'s, the outbox owned.) -/
def ownRaftPhysReady (c : CfgM) (r : Loc) (id : w64) (s : NState) (msl : GoSlice)
    (ms : List QMsg) (h : Bool) : IProp GF :=
  iprop(∃ (rsl sl1 sl2 : GoSlice) (ms1 ms2 : List QMsg),
    "#Hf_id" ∷ r.[raft, go!"id"] ↦□ id ∗
    "Hf_Term" ∷ r.[raft, go!"Term"] ↦ s.term ∗
    "Hf_Vote" ∷ r.[raft, go!"Vote"] ↦ s.vote ∗
    "Hf_readStates" ∷ r.[raft, go!"readStates"] ↦ rsl ∗
    "#HreadStates" ∷ readStatesPts rsl s.rd.states ∗
    "HreadStates_cap" ∷ ownSliceCap ReadState rsl (DFrac.own 1) ∗
    "Hf_raftLog" ∷ r.[raft, go!"raftLog"] ↦ s.log ∗
    "Hf_state" ∷ r.[raft, go!"state"] ↦ stateW64 s.role ∗
    "Hf_lead" ∷ r.[raft, go!"lead"] ↦ s.lead ∗
    "Hf_msgs" ∷ r.[raft, go!"msgs"] ↦ sl1 ∗
    "Hf_msgsAA" ∷ r.[raft, go!"msgsAfterAppend"] ↦ sl2 ∗
    "HmsgsAA" ∷ sl2 ↦* ms2.map QMsg.loc ∗
    "HmsgsAA_cap" ∷ ownSliceCap Loc sl2 (DFrac.own 1) ∗
    "%Houtbox" ∷ ⌜outboxRelP s.outbox ms1 ms2⌝ ∗
    "Hself" ∷ ([∗list] q ∈ ms2, selfOwn id q) ∗
    "Hother" ∷ ([∗list] q ∈ ms2, otherHalf id q) ∗
    "%HmsgsAA_ok" ∷ ⌜∀ m ∈ ms2, AAMsgOk id s.term m.st⌝ ∗
    "%Hout_term" ∷ ⌜∀ m ∈ ms1 ++ ms2, OutTermOk s.prevote s.term m.st.msg⌝ ∗
    "%Hgh_out" ∷ ⌜s.gh.outlb ≤ ms1.length + ms2.length⌝ ∗
    "%Hgh_unst" ∷ ⌜LogGhOk s s.logst⌝ ∗
    "%Hmslen" ∷ ⌜ms.length ≤ ms1.length + ms2.length⌝ ∗
    "Hundo" ∷ (msl ↦* ms.map QMsg.loc -∗ ownSliceCap Loc msl (DFrac.own 1) -∗
               ([∗list] q ∈ ms, msgOwn q.loc (readyDq q.st) q.st) -∗
               sl1 ↦* ms1.map QMsg.loc ∗ ownSliceCap Loc sl1 (DFrac.own 1) ∗
               ([∗list] q ∈ ms1, qOwn q) ∗
               ([∗list] q ∈ ms2.filter (fun q => !isSelfQ id q),
                 msgOwn q.loc (DFrac.own (1 : Qp).half) q.st)) ∗
    -- the log, after the storage's hand-out if `h` (2026-10-10, `ownRaftLog_handout`)
    "Hlog" ∷ ownRaftLog s.log (if h then logHanded s.logst else s.logst) ∗
    "Hclose" ∷ (∀ (sl1' sl2' : GoSlice) (ms1' ms2' : List QMsg) (o : List Msg)
                  (ls' : LogState) (g : NGhost) (rs' : GoSlice) (rd' : RdState),
        r.[raft, go!"Term"] ↦ s.term -∗
        r.[raft, go!"Vote"] ↦ s.vote -∗
        r.[raft, go!"readStates"] ↦ rs' -∗
        readStatesPts rs' rd'.states -∗ ownSliceCap ReadState rs' (DFrac.own 1) -∗
        ⌜rd'.ro = s.rd.ro ∧ rd'.pend = s.rd.pend⌝ -∗
        r.[raft, go!"raftLog"] ↦ s.log -∗
        r.[raft, go!"state"] ↦ stateW64 s.role -∗
        r.[raft, go!"lead"] ↦ s.lead -∗
        r.[raft, go!"msgs"] ↦ sl1' -∗ sl1' ↦* ms1'.map QMsg.loc -∗
        ownSliceCap Loc sl1' (DFrac.own 1) -∗
        r.[raft, go!"msgsAfterAppend"] ↦ sl2' -∗ sl2' ↦* ms2'.map QMsg.loc -∗
        ownSliceCap Loc sl2' (DFrac.own 1) -∗
        outboxRel o ms1' ms2' -∗
        ⌜∀ m ∈ ms2', AAMsgOk id s.term m.st⌝ -∗
        ⌜∀ m ∈ ms1' ++ ms2', OutTermOk s.prevote s.term m.st.msg⌝ -∗
        ⌜g.outlb ≤ ms1'.length + ms2'.length⌝ -∗
        ⌜g.unst = true → nextUnstable ls' ≠ [] ∨ ls'.snap ≠ none⌝ -∗
        ownRaftLog s.log ls' -∗
        ownRaftPhysCV c c.voters r id { s with outbox := o, logst := ls', gh := g, rd := rd' }))

/-! ### Read credits (see the file header) -/

/-- The number of `MsgReadIndex`s among messages (2026-10-16, stage R5: their states). -/
def rdCountM (ms : List MsgSt) : Nat :=
  ms.countP (fun m => decide (m.msg.Type' = MsgReadIndex))

omit [FfiInterp ffi] [FfiSemantics ext ffi] go_gctx in
theorem rdCountM_cons (m : MsgSt) (ms : List MsgSt) :
    rdCountM (m :: ms) = (if m.msg.Type' = MsgReadIndex then 1 else 0) + rdCountM ms := by
  unfold rdCountM
  rw [List.countP_cons]
  by_cases h : m.msg.Type' = MsgReadIndex <;> simp [h, Nat.add_comm]

omit [FfiInterp ffi] [FfiSemantics ext ffi] go_gctx in
theorem rdCountM_append (a b : List MsgSt) : rdCountM (a ++ b) = rdCountM a + rdCountM b := by
  unfold rdCountM; exact List.countP_append

omit [FfiInterp ffi] [FfiSemantics ext ffi] go_gctx in
theorem rdCountM_filter_le (l : List QMsg) (f : QMsg → Bool) :
    rdCountM ((l.filter f).map QMsg.st) ≤ rdCountM (l.map QMsg.st) := by
  unfold rdCountM
  rw [List.countP_map, List.countP_map]
  exact List.filter_sublist.countP_le

omit [FfiInterp ffi] [FfiSemantics ext ffi] go_gctx in
theorem mtypeOf_MsgReadIndex : mtypeOf MsgReadIndex = some .readIndex := rfl

omit [FfiInterp ffi] [FfiSemantics ext ffi] go_gctx in
/-- Only `MsgReadIndex` is abstracted as a `readIndex`. -/
theorem mtypeOf_readIndex (t : w32) (H : mtypeOf t = some .readIndex) : t = MsgReadIndex := by
  unfold mtypeOf at H
  split at H <;> simp_all
  rename_i h
  exact uint_Z_inj.1 (by rw [h]; rfl)

omit [FfiInterp ffi] [FfiSemantics ext ffi] go_gctx in
/-- A queued message contributes a read-index request to the abstract outbox iff it is a
`MsgReadIndex`. (2026-10-16, stage R5: pure.) -/
theorem msgAbs_rdCount (m : MsgSt) (a : Option Msg) (H : msgAbs m a) :
    rdCount a.toList = if m.msg.Type' = MsgReadIndex then 1 else 0 := by
  rcases H with H | ⟨ty, H1, -, rfl⟩ | ⟨sv, H1, -, rfl⟩
  · obtain ⟨Hn, rfl⟩ := H
    have Hne : m.msg.Type' ≠ MsgReadIndex := (mtypeOf_None_ne _ Hn).2.2.2.2.2.2.2.2.1
    simp [rdCount, Hne]
  · simp only [Option.toList_some, rdCount_singleton, absMsg, absMsgFrom]
    by_cases hty : ty = .readIndex
    · subst hty
      simp [mtypeOf_readIndex _ H1]
    · have Hne : m.msg.Type' ≠ MsgReadIndex := by
        intro h
        rw [h, mtypeOf_MsgReadIndex] at H1
        cases H1
        exact hty rfl
      simp [hty, Hne]
  · have Hne : m.msg.Type' ≠ MsgReadIndex := by
      intro h
      rw [h, mtypeOf_MsgReadIndex] at H1
      cases H1
    simp [rdCount, absSnap, absSnapFrom, Hne]

omit [FfiInterp ffi] [FfiSemantics ext ffi] go_gctx in
theorem msgsAbs_rdCount (ms : List QMsg) (as_ : List (Option Msg))
    (H : List.Forall₂ (fun q a => msgAbs q.st a) ms as_) :
    rdCountM (ms.map QMsg.st) = rdCount (absList as_) := by
  induction H with
  | nil => rfl
  | @cons q a ms as' Ha _ ih =>
    have Hab : absList (a :: as') = a.toList ++ absList as' := by cases a <;> rfl
    rw [List.map_cons, Hab, rdCount_append, msgAbs_rdCount _ _ Ha, ← ih, rdCountM_cons]

omit [FfiInterp ffi] [FfiSemantics ext ffi] go_gctx in
/-- The messages a `Ready` hands out (those of `r.msgs` and those of `msgsAfterAppend` to
others) hold at most as many `MsgReadIndex`s as the outbox has requests (2026-10-16). -/
theorem outboxRelP_rdCount (o : List Msg) (ms1 ms2 : List QMsg) (f : QMsg → Bool)
    (Hp : outboxRelP o ms1 ms2) :
    rdCountM ((ms1 ++ ms2.filter f).map QMsg.st) ≤ rdCount o := by
  obtain ⟨as1, as2, Ho, Hf1, Hf2⟩ := Hp
  have h1 := msgsAbs_rdCount ms1 as1 Hf1
  have h2 := msgsAbs_rdCount ms2 as2 Hf2
  have h3 := rdCountM_filter_le ms2 f
  have h4 : rdCount o = rdCount (absList as1 ++ absList as2) := List.Perm.countP_eq _ Ho
  rw [List.map_append, rdCountM_append, h4, rdCount_append, ← h1, ← h2]
  omega

/-- `rdCountM ms` credits are one per `MsgReadIndex` of `ms`. -/
theorem rdCred_msgs (γ : RaftNames) (ms : List QMsg) :
    rdCred (GF := GF) γ (rdCountM (ms.map QMsg.st)) ⊢
      [∗list] q ∈ ms, rdCred γ (if q.st.msg.Type' = MsgReadIndex then 1 else 0) := by
  induction ms with
  | nil => iintro _; iempintro
  | cons m ms IH =>
    iintro H
    rw [List.map_cons, rdCountM_cons]
    icases (rdCred_split γ _ _).1 $$ H with ⟨H1, H2⟩
    isplitl [H1]
    · iexact H1
    · iapply IH $$ H2

/-- The node between `readyWithoutAccept` and `acceptReady` (see the file header): the
conjuncts of `ownRawNode γ rn id rs` at a state `s` with an empty queue and nothing
unpersisted (`Ready`'s premises), the struct open with the outbox's messages handed out
(`ownRaftPhysReady`), and what `acceptReady` reads of `rd`: `rd.SoftState` `nil` or
read-only, no snapshot, the read states (if none, the node has none: `Hrdrs`), the
committed entries `ce` extending
`rs.delivered` (`isCommitted`) and the next ones after `applying` (`CeOk`), with their
slice's capacity, and the entries `es` handed out (`nextUnstable`). `ms` are the messages
handed out in `rd.Messages`, which `ownRawNodeReady_abandon` takes back (2026-10-10). Since
2026-10-13 (read credits, see the file header): once handed out (`h`), the ghost state is
at the drained outbox; the outbox's messages were legitimately sent (`Hout`), and `ms`
holds at most as many `MsgReadIndex`s as it has requests (`Hrdc`). (2026-10-16, stage R5:
`ms : List QMsg`, pointers and states, handed out at `readyDq`; `rd.HardState` `nil` or a
read-only hard state (`Hrdhard`: `hardState()`'s fresh one, which `acceptReady` stores in
`prevHardSt`); `rd.Snapshot` `nil`; the read states `readStatesPts`; the entries `entsRO`
(`Hce`, `Hents`), the committed entries' capacity a `[]*pb.Entry`'s; `prevHardSt` read-only
(`Hhard`); the queue `[]*pb.Message`.) -/
def ownRawNodeReady (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (rd : Ready)
    (ce es : List EntryM) (ms : List QMsg) (h : Bool := false) : IProp GF :=
  iprop(∃ (s : NState) (cf : CfgM) (fp : List EntryM) (rnv : RawNode) (sv : SoftState)
      (hprev : HardStateM),
  "Hrn" ∷ rawNodeOwn rn rnv ∗
  "Hphys" ∷ ownRaftPhysReady cf rnv.raft' id s rd.Messages' ms h ∗
  "Hghost" ∷ ownStepGhost γ (rs.mode.toG ⟨rs.capplied, rs.cfg, fp⟩) cf id
    (if h then { s with outbox := [] } else s) ∗
  "#Hsdrf" ∷ sdrOk rnv.raft' rs.mode ∗
  "#Hout" ∷ ([∗list] x ∈ s.outbox, isMessage γ x) ∗
  "%Hwf" ∷ ⌜NStateWf s⌝ ∗
  "%Hin" ∷ ⌜rs.mode = .static → id ∈ γ.reCfg⌝ ∗
  "%Hal" ∷ ⌜cf.autoLeave = false⌝ ∗
  "%Hasync" ∷ ⌜rnv.asyncStorageWrites' = false⌝ ∗
  "#Hsoft" ∷ rnv.prevSoftSt' ↦□ sv ∗
  "#Hhard" ∷ hsRO rnv.prevHardSt' hprev ∗
  "Hsteps" ∷ rnv.stepsOnAdvance' ↦* ([] : List Loc) ∗
  "Hsteps_cap" ∷ ownSliceCap Loc rnv.stepsOnAdvance' (DFrac.own 1) ∗
  "#Hcommitted" ∷ isCommitted γ (rs.delivered ++ ce) ∗
  "#Hstrecs" ∷ storedRecs γ s.logst.prev s.logst.stored ∗
  "%Hdlen" ∷ ⌜rs.delivered.length = (uint.Z s.logst.applying).toNat⌝ ∗
  "%Hunp" ∷ ⌜s.logst.unpersisted = []⌝ ∗
  "%Hsnap" ∷ ⌜s.logst.snap = none⌝ ∗
  "%Htrm" ∷ ⌜rs.term = s.term⌝ ∗
  "%Hstor" ∷ ⌜rs.storage = s.logst.storage⌝ ∗
  "%Hpvoff" ∷ ⌜s.prevote = false⌝ ∗
  "%Hrs_out" ∷ ⌜rs.outlb = s.gh.outlb⌝ ∗
  "%Hrs_unst" ∷ ⌜rs.unst = s.gh.unst⌝ ∗
  "%Hrs_clb" ∷ ⌜uint.Z rs.clb ≤ uint.Z s.logst.committed⌝ ∗
  -- the `Ready`, as `acceptReady` reads it
  "#Hrdsoft" ∷ (⌜rd.SoftState' = null⌝ ∨ ∃ v : SoftState, rd.SoftState' ↦□ v) ∗
  "#Hrdhard" ∷ (∃ hrd : HardStateM, hsOpt rd.HardState' hrd) ∗
  "%Hrdz" ∷ ⌜rd.Snapshot' = null⌝ ∗
  "#Hrdrs" ∷ (∃ sts : List ReadStateM, readStatesPts rd.ReadStates' sts ∗
    ⌜sts = [] → s.rd.states = []⌝) ∗
  "#Hce" ∷ entsRO rd.CommittedEntries' ce ∗
  "Hce_cap" ∷ ownSliceCap Loc rd.CommittedEntries' (DFrac.own 1) ∗
  "#Hents" ∷ entsRO rd.Entries' es ∗
  "%Hceok" ∷ ⌜CeOk s.logst ce⌝ ∗
  "%Hes" ∷ ⌜es = nextUnstable s.logst⌝ ∗
  "%Hrdc" ∷ ⌜rdCountM (ms.map QMsg.st) ≤ rdCount s.outbox⌝)

/-- Abandoning a computed `Ready` (2026-10-10; see the file header): with the messages it
handed out given back, the node is as before `readyWithoutAccept` (which changed nothing:
Go's "read-only operation"), but for the lower bounds (`RNState.outlb`, `unst`, `clb`),
raised to what the `Ready` held: at least as many messages as it handed out are queued,
unstable entries are still to be handed out if it handed some out, and its committed
entries are below the commit index. Every step keeps these, so if `HasReady` later finds
nothing new (`ownRawNodeIdle`), the `Ready` held no messages and no entries, and its
committed entries are still the next ones (`ownRawNodeIdle_ready`): `node.go`'s `run`
may then send it after all, as it does. The premises are `readyWithoutAccept`'s.
Everything else `readyWithoutAccept` allocated (the `Ready` itself, the committed
entries' slice) is dropped. (2026-10-16, stage R5: the messages handed out come back, at
`readyDq`, with `rd.Messages`' slice and capacity: D8.) -/
theorem ownRawNodeReady_abandon (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState)
    (rd : Ready) (ce es : List EntryM) (ms : List QMsg)
    (Hsteps0 : rs.steps = []) (Hunp0 : rs.unpersisted = []) :
    ⊢ rd.Messages' ↦* ms.map QMsg.loc -∗ ownSliceCap Loc rd.Messages' (DFrac.own 1) -∗
      ([∗list] q ∈ ms, msgOwn q.loc (readyDq q.st) q.st) -∗
      ownRawNodeReady (GF := GF) γ rn id rs rd ce es ms -∗
      ∃ (n : Nat) (u : Bool) (c : w64),
        ⌜ms.length ≤ n ∧ (es ≠ [] → u = true) ∧
         (∀ e, ce.getLast? = some e → uint.Z e.Index' ≤ uint.Z c ∧
           uint.Z e.Index' = (rs.delivered.length : Int) + (ce.length : Int))⌝ ∗
        ownRawNode γ rn id { rs with outlb := n, unst := u, clb := c } := by
  iintro Hmsgs Hmsgs_cap Hown H
  iunfold ownRawNodeReady at H
  icases H with ⟨%s, %c, %fp, %rnv, %sv, %hprev, H⟩
  iNamed H
  iunfold ownRaftPhysReady at Hphys
  icases Hphys with ⟨%rsl, %sl1, %sl2, %ms1, %ms2, Hphys⟩
  iNamed Hphys
  icases Hundo $$ Hmsgs Hmsgs_cap Hown with ⟨Hm1, Hc1, Hown1, Hhalf⟩
  ihave Hoth := (qOwns_other_halves id ms2).1 $$ [Hhalf Hother]
  · iframe Hhalf Hother
  ihave Hown2 := (qOwns_self_split id ms2).2 $$ [Hself Hoth]
  · iframe Hself Hoth
  ihave Hob := outboxRel_join s.outbox ms1 ms2 $$ [Hown1 Hown2]
  · iframe Hown1 Hown2; ipureintro; exact Houtbox
  simp only [Bool.false_eq_true, ↓reduceIte]
  let g : NGhost := { outlb := ms1.length + ms2.length,
                      unst := decide (nextUnstable s.logst ≠ []) }
  ihave Hphys := Hclose $$ %sl1 %sl2 %ms1 %ms2 %s.outbox %s.logst %g %rsl %s.rd Hf_Term Hf_Vote
    Hf_readStates HreadStates HreadStates_cap %(And.intro rfl rfl)
    Hf_raftLog Hf_state Hf_lead Hf_msgs Hm1 Hc1 Hf_msgsAA HmsgsAA HmsgsAA_cap
    Hob %HmsgsAA_ok %Hout_term %(Nat.le_refl _)
    %(fun h => .inl (of_decide_eq_true h)) Hlog
  ihave #Hdeliv : isCommitted γ rs.delivered $$ []
  · iapply isCommitted_mono γ rs.delivered (rs.delivered ++ ce) (List.prefix_append _ _)
      $$ Hcommitted
  ihave Hpend : pendList γ id ([] : List Loc) rs.steps $$ []
  · rw [Hsteps0]; iapply pendList_nil
  iexists ms1.length + ms2.length, decide (nextUnstable s.logst ≠ []), s.logst.committed
  isplitr
  · ipureintro
    refine ⟨Hmslen, fun h => by rw [Hes] at h; exact decide_eq_true h, fun e He => ?_⟩
    obtain ⟨-, H2, H3⟩ := Hceok e He
    refine ⟨H2, ?_⟩
    rw [H3, Hdlen]
    have := uint_Z_nonneg s.logst.applying
    omega
  let rs' : RNState :=
    { rs with outlb := ms1.length + ms2.length, unst := decide (nextUnstable s.logst ≠ []),
              clb := s.logst.committed }
  let s' : NState := { s with outbox := s.outbox, logst := s.logst, gh := g }
  ihave Hghost := ownStepGhost_congr γ _ c id (s := s) (s' := s') rfl rfl rfl rfl $$ Hghost
  iapply ownRawNode_intro γ rn id rs' s' c fp rnv sv hprev [] Hwf Hin Hal Hasync Hdlen
    (Hunp0.trans Hunp.symm) Hsnap (by show StepsOk _ rs.steps; rw [Hsteps0]; trivial) Htrm
    Hstor Hpvoff rfl rfl
    (Int.le_refl _)
    $$ Hrn Hphys Hghost Hsdrf Hsoft Hhard Hsteps Hsteps_cap Hpend Hdeliv Hstrecs

/-- The storage's hand-out for the entries a computed `Ready` hands out (2026-10-10): the
right to append them, ahead of `acceptReady` (`ownRaftLog_handout`). `node.go` runs it in
the atomic update of `readyc <- rd`, giving the right to the application with the `Ready`;
`acceptReady` takes the node after it. Since 2026-10-13 also the drain of the abstract
outbox (`Step.drain`, `ownRaftGhost_drain`), handing out with each message its read credit
(one for a `MsgReadIndex`). -/
theorem ownRawNodeReady_handout (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState)
    (rd : Ready) (ce es : List EntryM) (ms : List QMsg) :
    ⊢ ownRawNodeReady (GF := GF) γ rn id rs rd ce es ms false ==∗
      ownRawNodeReady γ rn id rs rd ce es ms true ∗ appendRight rs.storage es ∗
      [∗list] q ∈ ms, rdCred γ (if q.st.msg.Type' = MsgReadIndex then 1 else 0) := by
  iintro H
  iunfold ownRawNodeReady at H
  icases H with ⟨%s, %c, %fp, %rnv, %sv, %hprev, H⟩
  iNamed H
  iunfold ownRaftPhysReady at Hphys
  icases Hphys with ⟨%rsl, %sl1, %sl2, %ms1, %ms2, Hphys⟩
  iNamed Hphys
  simp only [Bool.false_eq_true, ↓reduceIte]
  imod ownRaftLog_handout _ _ Hunp Hsnap $$ Hlog with ⟨Hlog, Happ⟩
  iunfold ownStepGhost at Hghost
  icases Hghost with ⟨Hghost, Hrest⟩
  imod ownRaftGhost_drain γ id (toPState s) [] List.nil_subperm $$ Hghost with ⟨Hghost, Hcr⟩
  ihave Hrest := ghostRest_keep γ _ c id (s := s) (s' := { s with outbox := [] })
    rfl rfl rfl rfl rfl rfl rfl rfl $$ Hrest
  rw [show rdCount (toPState s).outbox - rdCount ([] : List Msg) =
      rdCountM (ms.map QMsg.st) + (rdCount s.outbox - rdCountM (ms.map QMsg.st)) by
    rw [show rdCount ([] : List Msg) = 0 from rfl]; show rdCount s.outbox - 0 = _; omega]
  icases (rdCred_split γ _ _).1 $$ Hcr with ⟨Hcr, -⟩
  ihave Hghost : ownStepGhost γ (rs.mode.toG ⟨rs.capplied, rs.cfg, fp⟩) c id
      { s with outbox := [] } $$ [Hghost Hrest]
  · iunfold ownStepGhost
    iframe Hrest
    rw [show toPState { s with outbox := [] } = { toPState s with outbox := [] } from rfl]
    iexact Hghost
  imodintro
  isplitr [Happ Hcr]
  · iunfold ownRawNodeReady
    iexists s, c, fp, rnv, sv, hprev
    simp only [named, ↓reduceIte]
    iframe Hrn Hghost Hout Hsdrf Hsoft Hhard Hsteps Hsteps_cap Hcommitted Hstrecs Hrdsoft
      Hrdhard Hrdrs Hce Hce_cap Hents
    isplitl
    · iunfold ownRaftPhysReady
      iexists rsl, sl1, sl2, ms1, ms2
      simp only [named, ↓reduceIte]
      iframe Hf_id Hf_Term Hf_Vote Hf_readStates HreadStates HreadStates_cap Hf_raftLog
        Hf_state Hf_lead Hf_msgs Hf_msgsAA HmsgsAA HmsgsAA_cap Hself Hother Hundo Hlog Hclose
      ipureintro
      exact ⟨Houtbox, HmsgsAA_ok, Hout_term, Hgh_out, Hgh_unst, Hmslen⟩
    ipureintro
    exact ⟨Hwf, Hin, Hal, Hasync, Hdlen, Hunp, Hsnap, Htrm, Hstor, Hpvoff, Hrs_out, Hrs_unst,
      Hrs_clb, Hrdz, Hceok, Hes, Hrdc⟩
  isplitl [Happ]
  · rw [Hes, ← Hstor]; iexact Happ
  iapply rdCred_msgs γ ms $$ Hcr

/-! ## A node with nothing new to hand out (2026-10-10)

`HasReady` returning `false` (`RawNode.HasReady.spec`) leaves the node as `ownRawNodeIdle`:
`ownRawNode` at a state with no queued message, no unstable entry still to be handed out,
no `ReadState` (2026-10-13), and so the lower bounds `outlb` and `unst` at their least (`ownRawNodeIdle_facts`). Its use:
`node.go`'s `run` keeps a `Ready` it computed earlier armed when `HasReady` is `false`,
and may send it; by the lower bounds that `Ready` held nothing but committed entries still
the next ones, and possibly a stale `SoftState`/`HardState` (which only reset what
`HasReady` compares against), and `ownRawNodeIdle_ready` turns the node back into
`ownRawNodeReady` for it, so that `acceptReady` takes it. -/

/-- See the section header. (2026-10-16, stage R5: `ownRawNode`'s conjuncts as they are now:
`Hhard`, the queue `pendList`.) -/
def ownRawNodeIdle (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) : IProp GF :=
  iprop(∃ (s : NState) (cf : CfgM) (fp : List EntryM) (rnv : RawNode) (sv : SoftState)
      (hprev : HardStateM) (steps : List Loc),
  "Hrn" ∷ rawNodeOwn rn rnv ∗
  "Hphys" ∷ ownRaftPhysCV cf cf.voters rnv.raft' id s ∗
  "Hghost" ∷ ownStepGhost γ (rs.mode.toG ⟨rs.capplied, rs.cfg, fp⟩) cf id s ∗
  "#Hsdrf" ∷ sdrOk rnv.raft' rs.mode ∗
  "%Hwf" ∷ ⌜NStateWf s⌝ ∗
  "%Hin" ∷ ⌜rs.mode = .static → id ∈ γ.reCfg⌝ ∗
  "%Hal" ∷ ⌜cf.autoLeave = false⌝ ∗
  "%Hasync" ∷ ⌜rnv.asyncStorageWrites' = false⌝ ∗
  "#Hsoft" ∷ rnv.prevSoftSt' ↦□ sv ∗
  "#Hhard" ∷ hsRO rnv.prevHardSt' hprev ∗
  "Hsteps" ∷ rnv.stepsOnAdvance' ↦* steps ∗
  "Hsteps_cap" ∷ ownSliceCap Loc rnv.stepsOnAdvance' (DFrac.own 1) ∗
  "Hpend" ∷ pendList γ id steps rs.steps ∗
  "#Hdeliv" ∷ isCommitted γ rs.delivered ∗
  "#Hstrecs" ∷ storedRecs γ s.logst.prev s.logst.stored ∗
  "%Hdlen" ∷ ⌜rs.delivered.length = (uint.Z s.logst.applying).toNat⌝ ∗
  "%Hunp" ∷ ⌜rs.unpersisted = s.logst.unpersisted⌝ ∗
  "%Hsnap" ∷ ⌜s.logst.snap = none⌝ ∗
  "%Hstok" ∷ ⌜StepsOk s rs.steps⌝ ∗
  "%Htrm" ∷ ⌜rs.term = s.term⌝ ∗
  "%Hstor" ∷ ⌜rs.storage = s.logst.storage⌝ ∗
  "%Hpvoff" ∷ ⌜s.prevote = false⌝ ∗
  "%Hrs_out" ∷ ⌜rs.outlb = s.gh.outlb⌝ ∗
  "%Hrs_unst" ∷ ⌜rs.unst = s.gh.unst⌝ ∗
  "%Hrs_clb" ∷ ⌜uint.Z rs.clb ≤ uint.Z s.logst.committed⌝ ∗
  -- nothing new: no queued message, no unstable entry still to be handed out, no
  -- `ReadState` (2026-10-13)
  "%Hidle" ∷ ⌜s.gh.outlb = 0 ∧ nextUnstable s.logst = [] ∧ s.rd.states = []⌝)

theorem ownRawNodeIdle_intro (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState)
    (s : NState) (c : CfgM) (fp : List EntryM) (rnv : RawNode) (sv : SoftState)
    (hprev : HardStateM) (steps : List Loc)
    (Hwf : NStateWf s) (Hin : rs.mode = .static → id ∈ γ.reCfg) (Hal : c.autoLeave = false)
    (Hasync : rnv.asyncStorageWrites' = false)
    (Hdlen : rs.delivered.length = (uint.Z s.logst.applying).toNat)
    (Hunp : rs.unpersisted = s.logst.unpersisted) (Hsnap : s.logst.snap = none)
    (Hstok : StepsOk s rs.steps)
    (Htrm : rs.term = s.term) (Hstor : rs.storage = s.logst.storage)
    (Hpvoff : s.prevote = false) (Hrs_out : rs.outlb = s.gh.outlb)
    (Hrs_unst : rs.unst = s.gh.unst) (Hrs_clb : uint.Z rs.clb ≤ uint.Z s.logst.committed)
    (Hidle : s.gh.outlb = 0 ∧ nextUnstable s.logst = [] ∧ s.rd.states = []) :
    ⊢ rawNodeOwn rn rnv -∗ ownRaftPhysCV c c.voters rnv.raft' id s -∗
      ownStepGhost (GF := GF) γ (rs.mode.toG ⟨rs.capplied, rs.cfg, fp⟩) c id s -∗
      sdrOk rnv.raft' rs.mode -∗
      rnv.prevSoftSt' ↦□ sv -∗ hsRO rnv.prevHardSt' hprev -∗ rnv.stepsOnAdvance' ↦* steps -∗
      ownSliceCap Loc rnv.stepsOnAdvance' (DFrac.own 1) -∗
      pendList γ id steps rs.steps -∗
      isCommitted γ rs.delivered -∗
      storedRecs γ s.logst.prev s.logst.stored -∗
      ownRawNodeIdle γ rn id rs := by
  iintro Hrn Hphys Hghost #Hsdrf #Hsoft #Hhard Hsteps Hcap Hpend #Hdeliv #Hstrecs
  unfold ownRawNodeIdle
  iexists s, c, fp, rnv, sv, hprev, steps
  simp only [named]
  iframe Hrn Hphys Hghost Hsdrf Hsoft Hhard Hsteps Hcap Hpend Hdeliv Hstrecs
  ipureintro
  exact ⟨Hwf, Hin, Hal, Hasync, Hdlen, Hunp, Hsnap, Hstok, Htrm, Hstor, Hpvoff, Hrs_out,
    Hrs_unst, Hrs_clb, Hidle⟩

theorem ownRawNodeIdle_ownRawNode (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) :
    ⊢ ownRawNodeIdle (GF := GF) γ rn id rs -∗ ownRawNode γ rn id rs := by
  iintro H
  iNamed H
  iapply ownRawNode_intro γ rn id rs s cf fp rnv sv hprev steps Hwf Hin Hal Hasync Hdlen Hunp Hsnap
    Hstok Htrm Hstor Hpvoff Hrs_out Hrs_unst Hrs_clb
    $$ Hrn Hphys Hghost Hsdrf Hsoft Hhard Hsteps Hsteps_cap Hpend Hdeliv Hstrecs

/-- What the client sees of an idle node: the lower bounds at their least, and the commit
index at most the committed log handed out (`applying`). -/
theorem ownRawNodeIdle_facts (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) :
    ⊢ ownRawNodeIdle (GF := GF) γ rn id rs -∗
      ⌜rs.outlb = 0 ∧ rs.unst = false⌝ ∗ ownRawNodeIdle γ rn id rs := by
  iintro H
  iNamed H
  icases ownRaftPhysC_gh cf rnv.raft' id s $$ Hphys with ⟨%Hgh, Hphys⟩
  isplitr
  · ipureintro
    refine ⟨Hrs_out.trans Hidle.1, ?_⟩
    rw [Hrs_unst]
    cases Hu : s.gh.unst
    · rfl
    · rcases Hgh Hu with H | H
      · exact absurd Hidle.2.1 H
      · exact absurd Hsnap H
  iapply ownRawNodeIdle_intro γ rn id rs s cf fp rnv sv hprev steps Hwf Hin Hal Hasync Hdlen Hunp
    Hsnap Hstok Htrm Hstor Hpvoff Hrs_out Hrs_unst Hrs_clb Hidle
    $$ Hrn Hphys Hghost Hsdrf Hsoft Hhard Hsteps Hsteps_cap Hpend Hdeliv Hstrecs

/-- Accepting, after all, a `Ready` computed earlier and abandoned (see the section
header): an idle node (no `Ready` outstanding: `rs.steps = []`, `rs.unpersisted = []`) is
`ownRawNodeReady` for a `Ready` `rd` that hands out no messages and no entries, whose
committed entries `ce` extend the committed log handed out and are the next ones up to
the commit index's lower bound (`ownRawNodeReady_abandon`'s third fact), and whose soft
state and snapshot are as `readyWithoutAccept` leaves them; its read states `sts` may be
any (2026-10-13): the idle node has none, which is all `acceptReady` needs. (2026-10-16,
stage R5: and its hard state any `hsOpt`, its entries `[]` read-only; the queues' messages,
none handed out, stay in the predicate: `r.msgs`' with half of `msgsAfterAppend`'s to others
inside `Hundo`.) -/
theorem ownRawNodeIdle_ready (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (rd : Ready)
    (ce : List EntryM) (sts : List ReadStateM) (hrd : HardStateM)
    (Hsteps0 : rs.steps = []) (Hunp0 : rs.unpersisted = [])
    (Hrdz : rd.Snapshot' = null)
    (Hce_ok : ∀ e, ce.getLast? = some e → uint.Z e.Index' ≤ uint.Z rs.clb ∧
      uint.Z e.Index' = (rs.delivered.length : Int) + (ce.length : Int)) :
    ⊢ (⌜rd.SoftState' = null⌝ ∨ ∃ v : SoftState, rd.SoftState' ↦□ v) -∗
      hsOpt rd.HardState' hrd -∗
      entsRO rd.CommittedEntries' ce -∗
      ownSliceCap Loc rd.CommittedEntries' (DFrac.own 1) -∗
      entsRO rd.Entries' [] -∗
      isCommitted γ (rs.delivered ++ ce) -∗ readStatesPts rd.ReadStates' sts -∗
      ownRawNodeIdle (GF := GF) γ rn id rs -∗ ownRawNodeReady γ rn id rs rd ce [] [] false := by
  iintro #Hrdsoft #Hrdh #Hce Hce_cap #Hents #Hcommitted #Hrsts H
  iNamed H
  ihave %Hlen := BigSepL2.bigSepL2_length $$ Hpend
  have Hsteps_nil : steps = [] := by
    rw [Hsteps0] at Hlen; exact List.eq_nil_of_length_eq_zero Hlen
  subst Hsteps_nil
  icases ownRaftPhysC_view cf rnv.raft' id s $$ Hphys with
    ⟨%rss, %sl1, %sl2, %ms1, %ms2, Hv⟩
  iNamed Hv
  ihave #Hout : ([∗list] x ∈ s.outbox, isMessage (GF := GF) γ x) $$ [Hghost]
  · iunfold ownStepGhost at Hghost
    icases Hghost with ⟨Hg, -⟩
    rw [show s.outbox = (toPState s).outbox from rfl]
    iapply ownRaftGhost_outbox _ _ _ $$ Hg
  ihave #Hrdrs : iprop(∃ sts : List ReadStateM, readStatesPts rd.ReadStates' sts ∗
      ⌜sts = [] → s.rd.states = []⌝) $$ []
  · iexists sts
    iframe Hrsts
    ipureintro; intro _; exact Hidle.2.2
  icases outboxRel_split _ _ _ $$ Houtbox with ⟨%Hob, Hown1, Hown2⟩
  icases (qOwns_self_split id ms2).1 $$ Hown2 with ⟨Hself, Hoth⟩
  icases (qOwns_other_halves id ms2).2 $$ Hoth with ⟨Hhalf, Hother⟩
  ihave #Hrdhard : iprop(∃ hrd : HardStateM, hsOpt rd.HardState' hrd) $$ []
  · iexists hrd; iexact Hrdh
  iunfold ownRawNodeReady
  iexists s, cf, fp, rnv, sv, hprev
  simp only [named, Bool.false_eq_true, ↓reduceIte]
  iframe Hrn Hghost Hsdrf Hout Hsoft Hhard Hsteps Hsteps_cap Hcommitted Hstrecs Hrdsoft Hrdrs
    Hce Hce_cap Hents Hrdhard
  isplitl
  · iunfold ownRaftPhysReady
    iexists rss, sl1, sl2, ms1, ms2
    simp only [named, Bool.false_eq_true, ↓reduceIte]
    iframe Hf_id Hf_Term Hf_Vote Hf_readStates HreadStates HreadStates_cap Hf_raftLog Hf_state
      Hf_lead Hf_msgs Hf_msgsAA HmsgsAA HmsgsAA_cap Hself Hother Hlog
    isplitr
    · ipureintro; exact Hob
    isplitr
    · ipureintro; exact HmsgsAA_ok
    isplitr
    · ipureintro; exact Hout_term
    isplitr
    · ipureintro; exact Hgh_out
    isplitr
    · ipureintro; exact Hgh_unst
    isplitr
    · ipureintro; simp
    isplitl [Hmsgs Hmsgs_cap Hown1 Hhalf]
    · iintro - - -
      iframe Hmsgs Hmsgs_cap Hown1 Hhalf
    iintro %sl1' %sl2' %ms1' %ms2' %o %ls' %g %rs' %rd' HfTerm HfVote Hfrs Hrs' Hrsc %Hrd'
      Hflog Hfst Hfld Hfm Hm Hmc Hfma Hma Hmac Hob' %H1 %H2 %H3 %H4 Hl
    iapply Hclose $$ %sl1' %sl2' %ms1' %ms2' %o %ls' %g %rs' %rd' HfTerm HfVote Hfrs Hrs' Hrsc
      %Hrd' Hflog Hfst Hfld Hfm Hm Hmc Hfma Hma Hmac Hob' %H1 %H2 %H3 %H4 Hl
  ipureintro
  refine ⟨Hwf, Hin, Hal, Hasync, Hdlen, Hunp0 ▸ Hunp.symm, Hsnap, Htrm, Hstor, Hpvoff, Hrs_out, Hrs_unst, Hrs_clb, Hrdz,
    fun e He => ?_, Hidle.2.1.symm, Nat.zero_le _⟩
  obtain ⟨H1, H2⟩ := Hce_ok e He
  have Hne : ce ≠ [] := by intro h; subst h; simp at He
  have : 0 < ce.length := List.length_pos_iff.2 Hne
  have := uint_Z_nonneg s.logst.applying
  refine ⟨by omega, by omega, by omega⟩

/-- The `ReadState`s of the protocol state, each `readStateOk` (2026-10-13): persistent,
copied out of `rdOwn`. -/
theorem ownRaftGhost_readStates (γ : RaftNames) (id : w64) (ps : PState) {md : Bool} :
    ⊢ ownRaftGhost (GF := GF) γ id ps md -∗ [∗list] st ∈ ps.rd.states, readStateOk γ st := by
  unfold ownRaftGhost
  iintro ⟨%γv, %voted, %kl, H⟩
  iNamed H
  iunfold rdOwn at Hrd
  icases Hrd with ⟨%γl, %rqm, -, -, -, -, -, #Hst0, -⟩
  iexact Hst0

/-- **A client's reading of a `ReadState`** (2026-10-13): the client that created the read
context `c` and finds `st`'s `RequestCtx` to be `c` learns `readOk γ c st.Index'`: its read
was created knowing a committed log no longer than the index. (2026-10-16, stage R5, D6: the
context is its bytes, so the client compares them, `Hc`; until then it registered its slice,
`isPropData γ rctx c`, and found `st`'s `RequestCtx` to be that slice.) -/
theorem readStateOk_readOk (γ : RaftNames) (st : ReadStateM) (c : List w8)
    (Hc : st.RequestCtx' = c) :
    ⊢ readStateOk (GF := GF) γ st -∗ readOk γ c st.Index' := by
  iintro #Hst
  iunfold readStateOk at Hst
  icases Hst with ⟨%c', %Hc', #Hok⟩
  rw [← Hc, Hc']
  iexact Hok

/-- ... and with the client's handle on its deposited read (2026-10-14, stage R), the read
witness: the update's results at every committed log at least `st.Index'` long
(`read_collect`). -/
theorem readStateOk_readWit (γ : RaftNames) (st : ReadStateM) (c : List w8)
    (Qr : List EntryM → IProp GF) (Hc : st.RequestCtx' = c) :
    ⊢ readStateOk (GF := GF) γ st -∗ isRead γ c Qr -∗ readWit γ c Qr st.Index' := by
  iintro #Hst #Hrd
  unfold readWit
  iframe Hrd
  iapply readStateOk_readOk γ st c Hc $$ Hst

/-- ... and with `readOk_prefix`: every committed log at least `st.Index'` long extends the
committed log `Lc` the read was created knowing (`readReq γ c Lc`), so applying the log up
to an index of at least `st.Index'` reads a state at least as new as the request. -/
theorem readStateOk_prefix (γ : RaftNames) (st : ReadStateM) (c : List w8)
    (Lc D : List EntryM) (Hc : st.RequestCtx' = c) (Hle : uint.Z st.Index' ≤ (D.length : Int)) :
    ⊢ readStateOk (GF := GF) γ st -∗ readReq γ c Lc -∗
      isCommitted γ D -∗ ⌜Lc <+: D⌝ := by
  iintro #Hst #Hrq #HD
  ihave #Hok := readStateOk_readOk γ st c Hc $$ Hst
  iapply readOk_prefix γ c st.Index' Lc D Hle $$ Hok Hrq HD

/-- The physical `ReadState`s are the protocol state's. -/
theorem toPState_rd_states (s : NState) : (toPState s).rd.states = s.rd.states := by
  by_cases h : s.role = .leader <;> simp [toPState, h, rdNL]

end rawnodeReady

end EtcdGrove
end Perennial
