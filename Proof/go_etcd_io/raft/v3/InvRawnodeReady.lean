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

`ownRaftPhysReady` is `ownRaftPhys` opened as `ownRaftPhysC_view` opens it, without the
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
hands out `rd.ReadStates ↦*□ sts` and each `ReadState`'s `readStateRaw`, persistent facts
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

public import Proof.go_etcd_io.raft.v3.ApiVocab
public import Proof.go_etcd_io.raft.v3.InvRawnode
public import Proof.go_etcd_io.raft.v3.LemmasCeFrozen
-- `ownRaftGhost_drain` (2026-10-13)
public import Proof.go_etcd_io.raft.v3.Protocol.Refinement
-- (D22 S-b) the hard state's witness, `hsWit`
public import Proof.go_etcd_io.raft.v3.Protocol.CommitWit

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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

-- The two halves joined at `AutoLeave = false` (the shares may disagree on it).
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
variable [GooseExts]

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

-- (2026-10-26, raft's signature, stage 1) `RespType` moved to `Proof.go_etcd_io.raft.v3.ApiVocab`.

-- (2026-10-26, raft's signature, stage 1) `readyDq` moved to `Proof.go_etcd_io.raft.v3.ApiVocab`.

/-- `msgsAfterAppend`'s messages to the node itself, which `acceptReady` queues. -/
def isSelfQ (id : w64) (q : QMsg) : Bool := decide (q.st.msg.To' = id)

/-- (D22 S-d3a, 2026-10-21) The log of a computed `Ready`: as it was, or once handed out (`h`) the
batch recorded as the application's (`logHanded`) and, with a snapshot (`lt`), the storage lent
(`ownRaftLog_lend`); (U8 v2) and the terms of the committed log handed out certified up to `dk`
(`ownRaftLog_certify`). -/
def rdyLog (h lt : Bool) (ls : LogState) (dk : Nat := ls.dtk) : LogState :=
  if h then logHanded (if lt then lendLog { ls with dtk := dk } else { ls with dtk := dk }) else ls

/-- (D22 S-d4; here since U8 v2) The committed log handed out after a `Ready` of the committed
entries `ce` and the loan `L`: `d ++ ce`, or with a snapshot the committed log up to it. -/
def dlvAfter (d ce : List EntryM) : Option SnapLoan → List EntryM
  | none => d ++ ce
  | some l => l.dlv

/-- (D22 S-d3a) What a snapshot `Ready` records of its loan (`SnapLoan`) at the node's state `s`:
the snapshot pending and not in progress, a snapshot the node may send, past index `0`; the
storage's floor; no committed entries handed out (`nextCommittedEnts`), the committed log up to the
snapshot extending `delivered`, `applying` at most the snapshot's index; and the batch handed out
the whole log after the snapshot (`ownRaftLog_snap_next`). -/
def SnapRdy (rs : RNState) (ce : List EntryM) (l : SnapLoan) (s : NState) : Prop :=
  s.logst.snap = some (snapId l.snap) ∧ s.logst.sip = false ∧
  snapTrip l.snap l.snap.Metadata'.ConfState'.lists ∈ s.logst.ksn ∧
  0 < uint.Z l.snap.Metadata'.Index' ∧ l.fl = s.logst.fl ∧ ce = [] ∧
  rs.delivered <+: l.dlv ∧ l.dlv.length = (uint.Z l.snap.Metadata'.Index').toNat ∧
  -- (D22 S-r, 2026-10-21) strictly: `applying` stays below a pending snapshot (`SipOk`)
  uint.Z s.logst.applying < uint.Z l.snap.Metadata'.Index' ∧
  nextUnstable s.logst = s.logst.sents ++ s.logst.uents ∧
  -- (2026-10-28, stage U0) its `ConfState` naming a node (`pendKsn`)
  ∃ x, l.snap.Metadata'.ConfState'.lists.Has x

end pure

section rawnodeReady
variable [GooseExts] [GooseSemantics] [GooseInterp]
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

omit [StorageModel GF] in
theorem mtypeOf_snap_eq (t : w32) (h : mtypeOf t = some .snap) : t = MsgSnap := by
  have h7 : uint.Z t = 7 := by
    unfold mtypeOf at h
    split at h <;> first | (cases h; done) | assumption | (simp at h)
  show t = W32 7
  word

/-- (D22 S-b′3, 2026-10-20) A queued message's certificate: none but a `MsgSnap`'s, whose
snapshot is certified (`raftSnapCert`); vacuous in the no-snapshot mode. What a `Ready` gets from
the storage's registry (`qSrc`) through the certificate link (`qCert_of_src`). -/
def qCert (γ : RaftNames) (q : QMsg) : IProp GF :=
  iprop(⌜γ.reNoSnap = true⌝ ∨ ⌜q.st.msg.Type' ≠ MsgSnap⌝ ∨ ∃ sv : SnapshotM, ⌜q.st.snap = some sv⌝ ∗
    raftSnapCertD γ (snapTrip sv sv.Metadata'.ConfState'.lists))

instance qCert_pers (γ : RaftNames) (q : QMsg) : Persistent (qCert (GF := GF) γ q) := by
  unfold qCert; infer_instance

/-- The queues' (`ownRaftPhys`'s `Hscert`, through the link). -/
def qCerts (γ : RaftNames) (l : List QMsg) : IProp GF := iprop([∗list] q ∈ l, qCert γ q)

instance qCerts_pers (γ : RaftNames) (l : List QMsg) : Persistent (qCerts (GF := GF) γ l) := by
  unfold qCerts; infer_instance

theorem qCerts_mem (γ : RaftNames) (l : List QMsg) (q : QMsg) (h : q ∈ l) :
    qCerts (GF := GF) γ l ⊢ qCert γ q := by
  unfold qCerts
  iintro #H
  ihave ⟨#Hq, -⟩ := BigSepL.bigSepL_mem_acc h $$ H
  iexact Hq

theorem qCerts_nil (γ : RaftNames) : ⊢ qCerts (GF := GF) γ [] := by
  unfold qCerts; iapply (BigSepL.bigSepL_nil (Φ := fun _ q => qCert (GF := GF) γ q)).2; iempintro

/-- A queued message's certificate's source, through the certificate link (U8 v2: over the
storage's names, `svCert`/`ksnCert`). -/
theorem qCert_of_src (γ : RaftNames) (sn : StorNames) (q : QMsg)
    (E : CoPset) (hE : ↑(raftCertN γ) ⊆ E) :
    ⊢ certLink (GF := GF) γ sn -∗ qSrc sn q ={E}=∗ qCert γ q := by
  iintro #Hok #Hs
  unfold qCert
  iunfold certLink at Hok
  iunfold qSrc at Hs
  iunfold tsSrc at Hs
  icases Hs with (%Hn | ⟨%sv, %Hsv, #Hc⟩)
  · imodintro; iright; ileft; ipureintro; exact Hn
  iunfold storCertOk at Hok
  icases Hok with ⟨#Hsv', #Hks, -⟩
  ihave Hc' : |={E}=> raftSnapCertD γ (snapTrip sv sv.Metadata'.ConfState'.lists) $$ [Hc]
  · icases Hc with (#Hc | #Hc)
    · iapply Hsv' $$ %_ %E %hE Hc
    · iapply Hks $$ %_ %E %hE Hc
  imod Hc' with #Hc'
  imodintro
  iright; iright
  iexists sv
  iframe Hc'
  ipureintro; exact Hsv

theorem qCerts_of_srcs (γ : RaftNames) (sn : StorNames) (l : List QMsg)
    (E : CoPset) (hE : ↑(raftCertN γ) ⊆ E) :
    ⊢ certLink (GF := GF) γ sn -∗ qSrcs sn l ={E}=∗ qCerts γ l := by
  induction l with
  | nil => iintro _ _; imodintro; iapply qCerts_nil
  | cons q l ih =>
    iintro #Hl #Hs
    iunfold qSrcs at Hs
    icases BigSepL.bigSepL_cons.1 $$ Hs with ⟨#Hq, #Hs⟩
    imod qCert_of_src γ sn q E hE $$ Hl Hq with #Hq'
    imod ih $$ Hl [Hs] with #Hl'
    · unfold qSrcs; iexact Hs
    imodintro
    unfold qCerts
    iapply BigSepL.bigSepL_cons.2
    iframe Hq'
    iexact Hl'

/-- (2026-10-28, the conf-change decision switch) The certificates of the snapshots the log knows
(`LogState.ksn`, `ownRaftLog`'s `Hkcert`), raft's, through the certificate link: what a `Ready`
handing out a pending snapshot reads its decisions from (`raftSnapCert_decs`). (U8 v2: over the
pins, `ksnCerts`.) -/
theorem ksnCerts_of_ok (γ : RaftNames) (sn : StorNames) (ks : List SnapTrip)
    (E : CoPset) (hE : ↑(raftCertN γ) ⊆ E) :
    ⊢ storCertOk (GF := GF) γ sn -∗ ksnCerts sn ks ={E}=∗
      [∗list] k ∈ ks, raftSnapCert γ k := by
  induction ks with
  | nil => iintro _ _; imodintro; iapply BigSepL.bigSepL_nil.2; iempintro
  | cons k ks ih =>
    iintro #Hok #Hs
    ihave #Hok' := Hok
    iunfold storCertOk at Hok'
    icases Hok' with ⟨-, #Hreg, -⟩
    iunfold ksnCerts at Hs
    icases BigSepL.bigSepL_cons.1 $$ Hs with ⟨#Hk, #Hs⟩
    imod Hreg $$ %k %E %hE Hk with #Hc
    iunfold raftSnapCertD at Hc
    icases Hc with ⟨#Hc, -⟩
    imod ih $$ Hok [Hs] with #Hr
    · unfold ksnCerts; iexact Hs
    imodintro
    iapply BigSepL.bigSepL_cons.2
    iframe Hc Hr

theorem ksnCerts_of_link (γ : RaftNames) (sn : StorNames) (ks : List SnapTrip)
    (E : CoPset) (hE : ↑(raftCertN γ) ⊆ E) :
    ⊢ certLink (GF := GF) γ sn -∗ ksnCerts sn ks ={E}=∗
      ⌜γ.reNoSnap = true⌝ ∨ [∗list] k ∈ ks, raftSnapCert γ k := by
  iintro #Hl #Hs
  iunfold certLink at Hl
  imod ksnCerts_of_ok γ sn ks E hE $$ Hl Hs with #Hr
  imodintro; iright; iexact Hr

/-- A queued message's contribution is in the outbox, so it was legitimately sent
(`isRaftMsg`, 2026-10-16): what `readyWithoutAccept` says of the messages it hands out, and
`acceptReady` of the self-addressed responses it queues. (D22 S-b′3) With its certificate
(`qCert`). -/
theorem outboxRelP_isRaftMsg (γ : RaftNames) (id : w64) (o : List Msg) (ms1 ms2 : List QMsg) (q : QMsg)
    (Hp : outboxRelP o ms1 ms2) (Hq : q ∈ ms1 ++ ms2)
    -- (2026-10-19, D21 M3) no snapshot in the outbox in the no-snapshot mode (`LogNsOk`)
    (Hns : γ.reNoSnap = true → ∀ x ∈ o, x.ty ≠ .snap)
    -- (2026-10-19, D21 M2r) and the message `SentMsgOk` in the no-transfer mode (`XfOk`; D22
    -- S-a to S-c: in it and the no-snapshot mode)
    (Hsent : γ.reNoXfer = true → SentMsgOk q.st)
    -- (2026-10-22, D38a) and no responses (`XfOk`)
    (Hrs : q.st.resps = [] ∧ AppFrom id q.st) :
    ([∗list] x ∈ o, isMessage (GF := GF) γ x) ⊢ qCert γ q -∗ isRaftMsg γ id q.st := by
  sorry -- PHASE1
  /- PHASE1-OLD
 by
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
  have Hnsnap : γ.reNoSnap = true → q.st.msg.Type' ≠ MsgSnap := by
    intro hns hty
    rcases Ha with ⟨Hn, -⟩ | ⟨ty', Hty', Hne, -⟩ | ⟨sv, -, -, rfl⟩
    · rw [hty, mtypeOf_MsgSnap] at Hn; cases Hn
    · rw [hty, mtypeOf_MsgSnap] at Hty'; cases Hty'; exact Hne rfl
    · exact Hns hns _ (Hin (absSnap q.st.msg sv sv.Metadata'.ConfState'.lists) (by simp)) rfl
  iintro #Ho #Hqc
  unfold isRaftMsg
  isplitr
  · ipureintro; exact Hnsnap
  isplitr
  · ipureintro; exact Hsent
  isplitr
  rotate_left
  isplitr
  rotate_left
  · ipureintro; exact Hrs
  rotate_left
  · -- (D22 S-r) the data certificate: the queue's, from the storage's registry
    unfold msgDat
    iintro !> %sv0 %Hsv0
    unfold qCert
    iunfold raftSnapCertD at Hqc
    icases Hqc with (%Hns' | %Hne | ⟨%sv, %Hsv, ⟨-, #Hd⟩⟩)
    · exact absurd Hsv0.1 (Hnsnap Hns')
    · exact absurd Hsv0.1 Hne
    · rw [Hsv] at Hsv0; obtain rfl := Option.some.inj Hsv0.2
      simp only [snapTrip, snapId]; iexact Hd
  iexists a
  isplitr
  · ipureintro; exact Ha
  cases a with
  | none => simp only [Option.toList_none]; iapply BigSepL.bigSepL_nil.2; iempintro
  | some x =>
    simp only [Option.toList_some]
    iapply BigSepL.bigSepL_singleton.2
    ihave #Hx := (BigSepL.bigSepL_mem (Φ := fun x => isMessage (GF := GF) γ x)
      (Hin x (by simp))) $$ Ho
    iapply isMessageC_intro $$ Hx
    -- (D22 S-b′3) the certificate: none but a snapshot's, the queue's
    unfold qCert
    iunfold raftSnapCertD at Hqc
    icases Hqc with (%Hns' | %Hne | ⟨%sv, %Hsv, ⟨#Hc, -⟩⟩)
    · iapply msgCert_of_ne
      exact Hns Hns' x (Hin x (by simp))
    · iapply msgCert_of_ne
      rcases Ha with ⟨-, h⟩ | ⟨ty', -, Hne', h⟩ | ⟨sv', Hty', -, -⟩
      · cases h
      · cases h; simp [absMsg, absMsgFrom, Hne']
      · exact absurd (mtypeOf_snap_eq _ Hty') Hne
    · rcases Ha with ⟨-, h⟩ | ⟨ty', -, Hne', h⟩ | ⟨sv', -, Hs', h⟩
      · cases h
      · iapply msgCert_of_ne; cases h; simp [absMsg, absMsgFrom, Hne']
      · cases h
        rw [Hsv] at Hs'; obtain rfl := Option.some.inj Hs'
        unfold msgCert; iright
        rw [show raftSnapCert (GF := GF) γ (msgSnapTrip (absSnap q.st.msg sv sv.Metadata'.ConfState'.lists)) =
          raftSnapCert γ (snapTrip sv sv.Metadata'.ConfState'.lists) from rfl]
        iexact Hc
  -/

/-- The abstraction of a message `isRaftMsg` covers, for a type the model describes but a
snapshot (2026-10-16): what `raft.Step`'s `Hmsg` asks of it. -/
theorem isRaftMsg_isMessage (γ : RaftNames) (id : w64) (st : MsgSt) (ty : MsgType)
    (Hty : mtypeOf st.msg.Type' = some ty) (Hns : ty ≠ .snap) :
    isRaftMsg (GF := GF) γ id st ⊢ isMessage γ (absMsg ty st.msg st.ents st.ctx) := by
  sorry -- PHASE1
  /- PHASE1-OLD
 by
  iintro #H
  unfold isRaftMsg
  icases H with ⟨-, -, ⟨%a, %Ha, #H⟩, -⟩
  rcases Ha with ⟨Hn, -⟩ | ⟨ty', Hty', -, rfl⟩ | ⟨sv, Hs, -, -⟩
  · rw [Hty] at Hn; cases Hn
  · rw [Hty] at Hty'; cases Hty'
    simp only [Option.toList_some]
    ihave #H := BigSepL.bigSepL_singleton.1 $$ H
    iapply isMessageC_isMessage $$ H
  · rw [Hty] at Hs; cases Hs; exact absurd rfl Hns
  -/

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
    (ms : List QMsg) (h : Bool) (lt : Bool := false) (dk : Nat := 0) : IProp GF :=
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
    "%Hout_term" ∷ ⌜∀ m ∈ ms1 ++ ms2, OutTermOk s.term s.gh.tc m.st.msg⌝ ∗
    "%Hgh_out" ∷ ⌜s.gh.outlb ≤ ms1.length + ms2.length⌝ ∗
    "%Hgh_unst" ∷ ⌜LogGhOk s s.logst⌝ ∗
    -- (2026-10-19, D21 M2r) the modes' facts of the queues
    "%Hxf" ∷ ⌜XfOk id s (ms1 ++ ms2)⌝ ∗
    -- (D22 S-b′3) the queues' certificates' source (`ownRaftPhys`'s `Hscert`)
    "#Hscert" ∷ qSrcs s.gh.sn (ms1 ++ ms2) ∗
    "%Hmslen" ∷ ⌜ms.length ≤ ms1.length + ms2.length⌝ ∗
    "Hundo" ∷ (msl ↦* ms.map QMsg.loc -∗ ownSliceCap Loc msl (DFrac.own 1) -∗
               ([∗list] q ∈ ms, msgOwn q.loc (readyDq q.st) q.st) -∗
               sl1 ↦* ms1.map QMsg.loc ∗ ownSliceCap Loc sl1 (DFrac.own 1) ∗
               ([∗list] q ∈ ms1, qOwn q) ∗
               ([∗list] q ∈ ms2.filter (fun q => !isSelfQ id q),
                 msgOwn q.loc (DFrac.own (1 : Qp).half) q.st)) ∗
    -- the log, after the storage's hand-out if `h` (2026-10-10, `ownRaftLog_handout`); (D22 S-d3a)
    -- with a snapshot (`lt`), the storage itself lent (`ownRaftLog_lend`)
    "Hlog" ∷ ownRaftLog s.log (rdyLog h lt s.logst dk) ∗
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
        ⌜∀ m ∈ ms1' ++ ms2', OutTermOk s.term g.tc m.st.msg⌝ -∗
        ⌜g.outlb ≤ ms1'.length + ms2'.length⌝ -∗
        ⌜GhLogOk g ls'⌝ -∗
        ⌜g.ns = s.gh.ns ∧ LogNsKeep s ls' ∧ ∀ m ∈ o, m ∈ s.outbox⌝ -∗
        ⌜s.role = .leader → uint.Z (logLast s.logst) ≤ uint.Z (logLast ls')⌝ -∗
        ⌜XfOk id { s with outbox := o, logst := ls', gh := g, rd := rd' } (ms1' ++ ms2')⌝ -∗
        qSrcs g.sn (ms1' ++ ms2') -∗
        ownRaftLog s.log ls' -∗
        ownRaftPhysCV c c.voters r id { s with outbox := o, logst := ls', gh := g, rd := rd' }))

/-- (D22 S-d3a) Before the hand-out, the lent flag is idle (`rdyLog false`). -/
theorem ownRaftPhysReady_lt0 (c : CfgM) (r : Loc) (id : w64) (s : NState) (msl : GoSlice)
    (ms : List QMsg) (lt lt' : Bool)
    (dk dk' : Nat) :
    ownRaftPhysReady (GF := GF) c r id s msl ms false lt dk ⊢
      ownRaftPhysReady c r id s msl ms false lt' dk' := by
  unfold ownRaftPhysReady rdyLog; exact .rfl

/-! ### Read credits (see the file header) -/

/-- The number of `MsgReadIndex`s among messages (2026-10-16, stage R5: their states). -/
def rdCountM (ms : List MsgSt) : Nat :=
  ms.countP (fun m => decide (m.msg.Type' = MsgReadIndex))

omit [GooseInterp] [GooseSemantics] go_gctx in
theorem rdCountM_cons (m : MsgSt) (ms : List MsgSt) :
    rdCountM (m :: ms) = (if m.msg.Type' = MsgReadIndex then 1 else 0) + rdCountM ms := by
  unfold rdCountM
  rw [List.countP_cons]
  by_cases h : m.msg.Type' = MsgReadIndex <;> simp [h, Nat.add_comm]

omit [GooseInterp] [GooseSemantics] go_gctx in
theorem rdCountM_append (a b : List MsgSt) : rdCountM (a ++ b) = rdCountM a + rdCountM b := by
  unfold rdCountM; exact List.countP_append

omit [GooseInterp] [GooseSemantics] go_gctx in
theorem rdCountM_filter_le (l : List QMsg) (f : QMsg → Bool) :
    rdCountM ((l.filter f).map QMsg.st) ≤ rdCountM (l.map QMsg.st) := by
  unfold rdCountM
  rw [List.countP_map, List.countP_map]
  exact List.filter_sublist.countP_le

-- (2026-10-26, raft's signature, stage 1) `mtypeOf_MsgReadIndex` moved to `Proof.go_etcd_io.raft.v3.ApiVocab`.

omit [GooseInterp] [GooseSemantics] go_gctx in
/-- Only `MsgReadIndex` is abstracted as a `readIndex`. -/
theorem mtypeOf_readIndex (t : w32) (H : mtypeOf t = some .readIndex) : t = MsgReadIndex := by
  unfold mtypeOf at H
  split at H <;> simp_all
  rename_i h
  exact uint_Z_inj.1 (by rw [h]; rfl)

omit [GooseInterp] [GooseSemantics] go_gctx in
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

omit [GooseInterp] [GooseSemantics] go_gctx in
theorem msgsAbs_rdCount (ms : List QMsg) (as_ : List (Option Msg))
    (H : List.Forall₂ (fun q a => msgAbs q.st a) ms as_) :
    rdCountM (ms.map QMsg.st) = rdCount (absList as_) := by
  induction H with
  | nil => rfl
  | @cons q a ms as' Ha _ ih =>
    have Hab : absList (a :: as') = a.toList ++ absList as' := by cases a <;> rfl
    rw [List.map_cons, Hab, rdCount_append, msgAbs_rdCount _ _ Ha, ← ih, rdCountM_cons]

omit [GooseInterp] [GooseSemantics] go_gctx in
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

/-! ### Proposal tickets (2026-10-19, D21 M6)

A queued `MsgProp` carries its entries' tickets (`entTk`); the abstract outbox keeps them
(`rdOwn`'s `msgsTks`), and a `Ready` hands each proposal it hands out its own (`stTks`). -/

-- (2026-10-26, raft's signature, stage 1) `stTks` moved to `Proof.go_etcd_io.raft.v3.ApiVocab`.

omit [GooseInterp] [GooseSemantics] go_gctx in
/-- Only `MsgProp` is abstracted as a `propose`. -/
theorem mtypeOf_propose (t : w32) (H : mtypeOf t = some .propose) : t = MsgProp := by
  unfold mtypeOf at H
  split at H <;> simp_all
  rename_i h
  exact uint_Z_inj.1 (by rw [h]; rfl)

/-- A queued proposal's abstraction. -/
def qProp (st : MsgSt) : Option Msg :=
  if st.msg.Type' = MsgProp then some (absMsg .propose st.msg st.ents st.ctx) else none

omit [GooseInterp] [GooseSemantics] go_gctx in
theorem msgAbs_props (m : MsgSt) (a : Option Msg) (H : msgAbs m a) :
    propsOf a.toList = (qProp m).toList := by
  unfold qProp
  rcases H with H | ⟨ty, H1, -, rfl⟩ | ⟨sv, H1, -, rfl⟩
  · obtain ⟨Hn, rfl⟩ := H
    have Hne : m.msg.Type' ≠ MsgProp := by
      intro h; rw [h, mtypeOf_MsgProp] at Hn; cases Hn
    simp [Hne]
  · by_cases hty : ty = .propose
    · subst hty
      simp [mtypeOf_propose _ H1, propsOf_cons, absMsg, absMsgFrom, Msg.mkV]
    · have Hne : m.msg.Type' ≠ MsgProp := by
        intro h; rw [h, mtypeOf_MsgProp] at H1; cases H1; exact hty rfl
      simp [Hne, propsOf_cons, absMsg, absMsgFrom, Msg.mkV, hty]
  · have Hne : m.msg.Type' ≠ MsgProp := by
      intro h; rw [h, mtypeOf_MsgProp] at H1; cases H1
    simp [Hne, propsOf_cons, absSnap, absSnapFrom]

omit [GooseInterp] [GooseSemantics] go_gctx in
theorem msgsAbs_props (ms : List QMsg) (as_ : List (Option Msg))
    (H : List.Forall₂ (fun q a => msgAbs q.st a) ms as_) :
    propsOf (absList as_) = ms.filterMap (fun q => qProp q.st) := by
  induction H with
  | nil => rfl
  | @cons q a ms as' Ha _ ih =>
    have Hab : absList (a :: as') = a.toList ++ absList as' := by cases a <;> rfl
    rw [Hab, propsOf_append, msgAbs_props _ _ Ha, ih, List.filterMap_cons]
    cases qProp q.st <;> rfl

omit [GooseInterp] [GooseSemantics] go_gctx in
/-- The proposals a `Ready` hands out are among the outbox's. -/
theorem outboxRelP_props (o : List Msg) (ms1 ms2 : List QMsg) (f : QMsg → Bool)
    (Hp : outboxRelP o ms1 ms2) :
    ((ms1 ++ ms2.filter f).filterMap (fun q => qProp q.st)).Subperm (propsOf o) := by
  obtain ⟨as1, as2, Ho, Hf1, Hf2⟩ := Hp
  have h1 := msgsAbs_props ms1 as1 Hf1
  have h2 := msgsAbs_props ms2 as2 Hf2
  have h4 : (propsOf o).Perm (propsOf (absList as1 ++ absList as2)) := Ho.filter _
  rw [propsOf_append, h1, h2] at h4
  refine List.Subperm.trans ?_ h4.symm.subperm
  rw [List.filterMap_append]
  exact (List.Sublist.append_left ((List.filter_sublist).filterMap _) _).subperm

/-- A proposal's abstraction carries its tickets. -/
theorem msgsTks_qProp (γ : RaftNames) (ms : List QMsg) :
    msgsTks (GF := GF) γ (ms.filterMap (fun q => qProp q.st)) ⊢ [∗list] q ∈ ms, stTks γ q.st := by
  induction ms with
  | nil => iintro -; iempintro
  | cons q ms ih =>
    iintro H
    rw [List.filterMap_cons]
    iapply (BigSepL.bigSepL_cons (Φ := fun _ (q : QMsg) => stTks (GF := GF) γ q.st)).2
    by_cases h : q.st.msg.Type' = MsgProp
    · have hq : qProp q.st = some (absMsg .propose q.st.msg q.st.ents q.st.ctx) := by
        unfold qProp; rw [if_pos h]
      rw [hq]
      simp only []
      iunfold msgsTks at H
      icases (BigSepL.bigSepL_cons (Φ := fun _ m => msgTks (GF := GF) γ m)).1 $$ H with ⟨H1, H2⟩
      isplitl [H1]
      · unfold stTks msgTks
        rw [if_pos h]
        simp only [absMsg, absMsgFrom, Msg.mkV, ↓reduceIte]
        iexact H1
      · iapply ih
        iunfold msgsTks
        iexact H2
    · have hq : qProp q.st = none := by unfold qProp; rw [if_neg h]
      rw [hq]
      simp only []
      isplitr
      · unfold stTks; rw [if_neg h]; iempintro
      iapply ih $$ H

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

-- (2026-10-26, raft's signature, stage 1) `softStateRO` moved to `Proof.go_etcd_io.raft.v3.ApiVocab`.

-- (2026-10-26, raft's signature, stage 1) `softStateRO_persistent` moved to `Proof.go_etcd_io.raft.v3.ApiVocab`.

/-- From the whole struct read-only (how the node holds it). -/
theorem softStateRO_of_opt (p : Loc) :
    (⌜p = null⌝ ∨ ∃ v : SoftState, p ↦□ v : IProp GF) ⊢ softStateRO p := by
  iintro H
  unfold softStateRO
  icases H with (%Hn | ⟨%v, H⟩)
  · ileft; ipureintro; exact Hn
  iright
  icases typedPointsto_split _ _ _ $$ H with H
  simp only [TypedPointsto.typedPointstoDef]
  iNamed H
  iexists v.Lead', v.RaftState'
  iframe Lead RaftState

/-- (D22 S-d3a, 2026-10-21) A computed `Ready`'s snapshot, as the node keeps it: none (`rd.Snapshot`
`nil`, no snapshot pending), or the loan `l` (`SnapRdy`) with half of the snapshot (the
application holds the other: the queued acknowledgement will share the pointer) and the committed
log up to it. -/
def rdSnapRel (γ : RaftNames) (rs : RNState) (rd : Ready) (ce : List EntryM) (L : Option SnapLoan)
    (s : NState) : IProp GF :=
  match L with
  | none => iprop(⌜rd.Snapshot' = null ∧ s.logst.snap = none⌝)
  | some l => iprop(ownSnapM l.ptr (DFrac.own (1 : Qp).half) l.snap ∗ isCommitted γ l.dlv ∗
      loanDec γ l ∗ ⌜l.ptr = rd.Snapshot' ∧ SnapRdy rs ce l s⌝)

/-- (D22 S-d3a, 2026-10-21) What the application learns of a `Ready`'s snapshot (`L`): none
(`rd.Snapshot` `nil`), or the loan's -- half of the snapshot (`ApplySnapshot`'s; the queued
acknowledgement shares the pointer), the committed log up to it (`isCommitted`, extending
`delivered`), no committed entries, the snapshot's index past `0`, within the storage's bound and
at least the floor the storage is lent at, and the entries handed out numbered right after it. -/
def LoanOut (rs : RNState) (rd : Ready) (ce es : List EntryM) (l : SnapLoan) : Prop :=
  l.ptr = rd.Snapshot' ∧ ce = [] ∧ rs.delivered <+: l.dlv ∧
  -- (D22 S-r, 2026-10-21) past the committed log handed out (`restore` is past the commit index):
  -- an application's own snapshot, at most the log it applied, is older
  rs.delivered.length < l.dlv.length ∧
  l.dlv.length = (uint.Z l.snap.Metadata'.Index').toNat ∧
  0 < uint.Z l.snap.Metadata'.Index' ∧ uint.Z l.snap.Metadata'.Index' < 2^61 ∧
  uint.Z l.fl ≤ uint.Z l.snap.Metadata'.Index' ∧ LogIndicesOk (snapId l.snap) es

def rdSnapOut (γ : RaftNames) (rs : RNState) (rd : Ready) (ce es : List EntryM)
    (L : Option SnapLoan) : IProp GF :=
  match L with
  | none => iprop(⌜rd.Snapshot' = null⌝)
  -- (D22 S-d4 item 4) the application's half set: `MemoryStorage.ApplySnapshot` takes it
  | some l => iprop(ownSnapS l.ptr (DFrac.own (1 : Qp).half) l.snap ∗ isCommitted γ l.dlv ∗
      ⌜LoanOut rs rd ce es l⌝)

-- (2026-10-26, raft's signature, stage 1) `readyOut` moved to `Proof.go_etcd_io.raft.v3.ApiVocab`.

-- (2026-10-26, raft's signature, stage 1) `snapReceipt` moved to `Proof.go_etcd_io.raft.v3.ApiVocab`.

/-- (D22 S-d3a) What `Advance` takes back: nothing, or the loan's receipt. -/
def loanRet (rs : RNState) : IProp GF :=
  match rs.slent with
  | none => iprop(emp)
  | some l => snapReceipt rs.storage l rs.unpersisted

/-- (2026-10-28, stage U3c) The configuration a snapshot's acknowledgement installs, in the mode `md`,
of the committed log `L` up to the snapshot: dynamically the fold of `L` (`StepR.applySnap`; the
snapshot's certificate makes it some, `SnapAckDyn`), `c` if none; statically `c` (unconstrained).
(2026-10-28, the decision switch) The fold over the decisions `M` (the loan's, `SnapLoan.decs`). -/
def RNMode.foldCfg : RNMode → DecMap → List EntryM → CCState → CCState
  | .static, _, _, c => c
  | .dyn dec c0 _ _, M, L, c => (cfgFold (effDec dec M) c0 L).getD c

/-- (2026-10-28, stage U3d) **The driver's view of the configuration after `Advance`** of a `Ready`
with the loan `L` (`node.Advance`), from `x` (its configuration index and configuration) before:
after a snapshot `Ready`, dynamically, at the snapshot's index and the fold of its committed log
(what `advRS` installs, `RNMode.foldCfg`); otherwise `x`. -/
def loanCfg (md : RNMode) (L : Option SnapLoan) (x : Nat × CCState) : Nat × CCState :=
  match L with
  | none => x
  | some l => if md.isDyn then (l.dlv.length, md.foldCfg l.decs l.dlv x.2) else x

theorem loanCfg_none (md : RNMode) (x : Nat × CCState) : loanCfg md none x = x := rfl

/-- (U3d) The view the driver expects back on `advancec` after a `Ready` with the loan `L`: none
without a snapshot (the driver keeps its view), `loanCfg` after one. -/
def loanReq (md : RNMode) (L : Option SnapLoan) (x : Nat × CCState) : Option (Nat × CCState) :=
  L.map fun _ => loanCfg md L x

theorem loanCfg_static {md : RNMode} (h : md.isDyn = false) (L : Option SnapLoan)
    (x : Nat × CCState) : loanCfg md L x = x := by
  cases L <;> simp [loanCfg, h]

/-- (D22 S-d3a) The node after `Advance` (`RawNode.Advance.spec`): the queue stepped, the term `t`,
the configuration index `ca`, the floor no longer raised; after a snapshot `Ready` also the loan
returned, nothing unpersisted and the committed log handed out up to the snapshot; (2026-10-28, stage
U3c) dynamically the configuration the snapshot's (`RNMode.foldCfg`), `ca` its index. -/
def advRS (rs : RNState) (t : w64) (ca : Nat) : RNState :=
  match rs.slent with
  | none => { rs with steps := [], term := t, capplied := ca, flw := false }
  | some l => { rs with steps := [], term := t, capplied := ca, flw := false, slent := none,
                        unpersisted := [], delivered := l.dlv, cfg := rs.mode.foldCfg l.decs l.dlv rs.cfg }

theorem advRS_none {rs : RNState} (t : w64) (ca : Nat) (h : rs.slent = none) :
    advRS rs t ca = { rs with steps := [], term := t, capplied := ca, flw := false } := by
  unfold advRS; rw [h]

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
    (ce es : List EntryM) (ms : List QMsg) (h : Bool := false) (L : Option SnapLoan := none) :
    IProp GF :=
  iprop(∃ (s : NState) (cf : CfgM) (fp : List EntryM) (ds : DecMap) (rnv : RawNode) (sv : SoftState)
      (hprev : HardStateM),
  "Hrn" ∷ rawNodeOwn rn rnv ∗
  "Hphys" ∷ ownRaftPhysReady cf rnv.raft' id s rd.Messages' ms h L.isSome
    (dlvAfter rs.delivered ce L).length ∗
  "Hghost" ∷ ownStepGhost γ (rs.mode.toG ⟨rs.capplied, rs.cfg, fp, ds⟩) cf id
    (if h then { s with outbox := [] } else s) ∗
  "#Hsdrf" ∷ sdrOk rnv.raft' rs.mode ∗
  "#Hout" ∷ ([∗list] x ∈ s.outbox, isMessage γ x) ∗
  "%Hwf" ∷ ⌜NStateWf s⌝ ∗
  "%Hin" ∷ ⌜rs.mode = .static → id ∈ γ.reCfg⌝ ∗
  "%Hasync" ∷ ⌜rnv.asyncStorageWrites' = false⌝ ∗
  "#Hsoft" ∷ rnv.prevSoftSt' ↦□ sv ∗
  "#Hhard" ∷ prevHS γ rnv.prevHardSt' hprev rs.phs ∗
  "Hsteps" ∷ rnv.stepsOnAdvance' ↦* ([] : List Loc) ∗
  "Hsteps_cap" ∷ ownSliceCap Loc rnv.stepsOnAdvance' (DFrac.own 1) ∗
  "#Hcommitted" ∷ isCommitted γ (rs.delivered ++ ce) ∗
  -- (D22 S-d3a) as `ownRawNode`'s: no restore since the last `Ready`
  "#Hstrecs" ∷ ackInv γ rs s ∗
  "%Hdlen" ∷ ⌜rs.delivered.length = (uint.Z s.logst.applying).toNat⌝ ∗
  "%Hunp" ∷ ⌜s.logst.unpersisted = []⌝ ∗
  -- (D22 S-d3a) as `ownRawNode`'s (a snapshot may be pending), and no loan
  "%Hsnap" ∷ ⌜rs.psnap = false ∧ rs.slent = none → s.logst.snap = none⌝ ∗
  "%Hloan" ∷ ⌜LoanOk rs s ∧ rs.slent = none⌝ ∗
  "%Htrm" ∷ ⌜rs.term = s.term⌝ ∗
  "%Hstor" ∷ ⌜rs.storage = s.logst.storage ∧ rs.sn = s.logst.sn⌝ ∗
  "%Hpvoff" ∷ ⌜RNPv rs fp s⌝ ∗
  "%Hrs_out" ∷ ⌜rs.outlb = s.gh.outlb⌝ ∗
  "%Hrs_unst" ∷ ⌜rs.unst = s.gh.unst⌝ ∗
  "%Hrs_clb" ∷ ⌜uint.Z rs.clb ≤ uint.Z s.logst.committed⌝ ∗
  -- (D19i part 1) the floor at most `applied` unless raised; `applied` at `applying` (no
  -- `Advance` outstanding)
  "%Hrnfl" ∷ ⌜(rs.flw = false → uint.Z s.logst.fl ≤ uint.Z s.logst.applied) ∧
    uint.Z s.logst.applying ≤ uint.Z s.logst.applied⌝ ∗
  -- the `Ready`, as `acceptReady` reads it
  "#Hrdsoft" ∷ (⌜rd.SoftState' = null⌝ ∨ ∃ v : SoftState, rd.SoftState' ↦□ v) ∗
  -- (D22l) with its witness (`phsWit`), for `prevHardSt`'s
  "#Hrdhard" ∷ (∃ hrd : HardStateM, hsOpt rd.HardState' hrd ∗ phsWit γ hrd) ∗
  -- (D22 S-d3a) the `Ready`'s snapshot (until then `nil`): none, or the loan `L`
  "Hrdz" ∷ rdSnapRel γ rs rd ce L s ∗
  "#Hrdrs" ∷ (∃ sts : List ReadStateM, readStatesPts rd.ReadStates' sts ∗
    ⌜sts = [] → s.rd.states = []⌝) ∗
  "#Hce" ∷ entsRO rd.CommittedEntries' ce ∗
  "Hce_cap" ∷ ownSliceCap Loc rd.CommittedEntries' (DFrac.own 1) ∗
  "#Hents" ∷ entsRO rd.Entries' es ∗
  "%Hceok" ∷ ⌜CeOk s.logst ce⌝ ∗
  "%Hes" ∷ ⌜es = nextUnstable s.logst⌝ ∗
  "%Hrdc" ∷ ⌜rdCountM (ms.map QMsg.st) ≤ rdCount s.outbox⌝ ∗
  -- (2026-10-19, D21 M6) and its proposals are among the outbox's (their tickets)
  "%Hprc" ∷ ⌜(ms.filterMap (fun q => qProp q.st)).Subperm (propsOf s.outbox)⌝ ∗
  -- (2026-10-19, D21 M3) no snapshot in the outbox in the no-snapshot mode (`LogNsOk`,
  -- `NsLink`): what the handed-out messages' `isRaftMsg` says
  "%Hnsout" ∷ ⌜γ.reNoSnap = true → ∀ x ∈ s.outbox, x.ty ≠ .snap⌝ ∗
  -- (2026-10-26, D22 J2, R-loc) as `ownRawNode`'s: the pending snapshot's receiver-local fact
  "#Hsloc" ∷ snapLocOk γ id s.logst.snap ∗
  -- (2026-10-28, stage U4a) the record of the storage's terms
  "%Hsdt" ∷ ⌜SdtTie rs s⌝)

/-- (D22 S-d3a) `loanCom` with no loan. -/
theorem loanCom_none (γ : RaftNames) {o : Option SnapLoan} (h : o = none) :
    ⊢ loanCom (GF := GF) γ o := by
  subst h; unfold loanCom; ipureintro; trivial

/-- (D22 S-d3a) `lentPend` with no loan. -/
theorem lentPend_none {o : Option SnapLoan} (h : o = none) (P : IProp GF) :
    P ⊢ lentPend o P := by
  subst h; exact .rfl

/-- ... and out. -/
theorem lentPend_none_elim {o : Option SnapLoan} (h : o = none) (P : IProp GF) :
    lentPend o P ⊢ P := by
  subst h; exact .rfl

/-- The `Ready`'s `SoftState`, read-only for the application (`softStateRO`; 2026-10-16, stage R7a):
from `Hrdsoft`, keeping the node. -/
theorem ownRawNodeReady_softStateRO (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState)
    (rd : Ready) (ce es : List EntryM) (ms : List QMsg) (h : Bool) (L : Option SnapLoan) :
    ownRawNodeReady (GF := GF) γ rn id rs rd ce es ms h L ⊢
      softStateRO rd.SoftState' ∗ ownRawNodeReady γ rn id rs rd ce es ms h L := by
  iintro H
  ihave #Hss : softStateRO rd.SoftState' $$ [H]
  · iunfold ownRawNodeReady at H
    icases H with ⟨%s, %cf, %fp, %ds, %rnv, %sv, %hprev, H⟩
    iNamed H
    iapply softStateRO_of_opt $$ Hrdsoft
  iframe Hss H

/-- (2026-10-26, D22 J2, R-loc) **A computed `Ready`'s snapshot is local to the node**: the
pending snapshot is the loan's (`SnapRdy`), whose receiver-local fact the node keeps (`Hsloc`). -/
theorem ownRawNodeReady_loanLoc (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState)
    (rd : Ready) (ce es : List EntryM) (ms : List QMsg) (h : Bool) (l : SnapLoan) :
    ownRawNodeReady (GF := GF) γ rn id rs rd ce es ms h (some l) ⊢
      snapLocal γ id l.snap.Metadata'.Index' ∗ ownRawNodeReady γ rn id rs rd ce es ms h (some l) := by
  iintro H
  ihave #Hss : snapLocal γ id l.snap.Metadata'.Index' $$ [H]
  · iunfold ownRawNodeReady at H
    icases H with ⟨%s, %cf, %fp, %ds, %rnv, %sv, %hprev, H⟩
    iNamed H
    unfold rdSnapRel
    icases Hrdz with ⟨-, -, -, %Hr⟩
    rw [show l.snap.Metadata'.Index' = (snapId l.snap).index' from rfl]
    iapply (snapLocOk_some γ id (snapId l.snap)).1
    rw [← Hr.2.1]; iexact Hsloc
  iframe Hss H

/-- (2026-10-28, the conf-change decision switch) A computed `Ready`'s loan has its decisions
(`loanDec`, `rdSnapRel`). -/
theorem ownRawNodeReady_loanDec (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState)
    (rd : Ready) (ce es : List EntryM) (ms : List QMsg) (h : Bool) (L : Option SnapLoan) :
    ownRawNodeReady (GF := GF) γ rn id rs rd ce es ms h L ⊢
      loanDecO γ L ∗ ownRawNodeReady γ rn id rs rd ce es ms h L := by
  iintro H
  ihave #Hd : loanDecO γ L $$ [H]
  · iunfold ownRawNodeReady at H
    icases H with ⟨%s, %cf, %fp, %ds, %rnv, %sv, %hprev, H⟩
    iNamed H
    cases L with
    | none => unfold loanDecO; itrivial
    | some l =>
      unfold rdSnapRel
      icases Hrdz with ⟨-, -, #Hd, -⟩
      unfold loanDecO; iexact Hd
  iframe Hd H

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
`readyDq`, with `rd.Messages`' slice and capacity: D8.) (D22 S-d3a, 2026-10-21) With a snapshot
(`L`) too: the node's half of the clone is dropped, as the application's may be. -/
theorem ownRawNodeReady_abandon (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState)
    (rd : Ready) (ce es : List EntryM) (ms : List QMsg) (L : Option SnapLoan)
    (Hsteps0 : rs.steps = []) (Hunp0 : rs.unpersisted = []) :
    ⊢ rd.Messages' ↦* ms.map QMsg.loc -∗ ownSliceCap Loc rd.Messages' (DFrac.own 1) -∗
      ([∗list] q ∈ ms, msgOwn q.loc (readyDq q.st) q.st) -∗
      ownRawNodeReady (GF := GF) γ rn id rs rd ce es ms false L -∗
      ∃ (n : Nat) (u : Bool) (c : w64),
        ⌜ms.length ≤ n ∧ (es ≠ [] → u = true) ∧
         (∀ e, ce.getLast? = some e → uint.Z e.Index' ≤ uint.Z c ∧
           uint.Z e.Index' = (rs.delivered.length : Int) + (ce.length : Int))⌝ ∗
        ownRawNode γ rn id { rs with outlb := n, unst := u, clb := c } := by
  sorry -- PHASE1
  /- PHASE1-OLD
 by
  iintro Hmsgs Hmsgs_cap Hown H
  iunfold ownRawNodeReady at H
  icases H with ⟨%s, %c, %fp, %ds, %rnv, %sv, %hprev, H⟩
  iNamed H
  iclear Hrdz
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
  ihave Hlog : ownRaftLog s.log s.logst $$ [Hlog]
  · iExactEq Hlog; rfl
  let g : NGhost := { s.gh with outlb := ms1.length + ms2.length, unst := decide (nextUnstable s.logst ≠ []) }
  ihave Hphys := Hclose $$ %sl1 %sl2 %ms1 %ms2 %s.outbox %s.logst %g %rsl %s.rd Hf_Term Hf_Vote
    Hf_readStates HreadStates HreadStates_cap %(And.intro rfl rfl)
    Hf_raftLog Hf_state Hf_lead Hf_msgs Hm1 Hc1 Hf_msgsAA HmsgsAA HmsgsAA_cap
    Hob %HmsgsAA_ok %Hout_term %(Nat.le_refl _)
    %(⟨fun h => .inl (of_decide_eq_true h), Hgh_unst.1.2⟩ : GhLogOk g s.logst)
    %(⟨rfl, fun _ => ⟨rfl, rfl, rfl, Int.le_refl _⟩, fun _ h => h⟩ :
      g.ns = s.gh.ns ∧ LogNsKeep s s.logst ∧ ∀ m ∈ s.outbox, m ∈ s.outbox)
    %(fun _ => Int.le_refl _) %(Hxf.of_fields rfl rfl rfl rfl) Hscert Hlog
  ihave #Hdeliv : isCommitted γ rs.delivered $$ []
  · iapply isCommitted_mono γ rs.delivered (rs.delivered ++ ce) (List.prefix_append _ _)
      $$ Hcommitted
  ihave Hpend : lentPend rs.slent (pendList γ id ([] : List Loc) rs.steps) $$ []
  · iapply lentPend_none Hloan.2; rw [Hsteps0]; iapply pendList_nil
  ihave #Hlc := loanCom_none γ Hloan.2
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
  iapply ownRawNode_intro γ rn id rs' s' c fp rnv sv hprev [] Hwf Hin Hasync Hdlen
    (Hunp0.trans Hunp.symm) Hsnap (by show StepsOk _ rs.steps; rw [Hsteps0]; trivial) Htrm
    Hstor Hpvoff rfl rfl
    (Int.le_refl _) ⟨Hrnfl.1, fun h => absurd Hrnfl.2 (Int.not_le.2 h)⟩ Hloan.1
    Hsdt $$ Hrn Hphys Hghost Hsdrf Hsoft Hhard Hsteps Hsteps_cap Hpend Hdeliv Hstrecs Hlc Hsloc
  -/

-- (2026-10-26, raft's signature, stage 1) `readyIdx` moved to `Proof.go_etcd_io.raft.v3.ApiVocab`.

-- (2026-10-26, raft's signature, stage 1) `readyIdx_persistent` moved to `Proof.go_etcd_io.raft.v3.ApiVocab`.

omit [GooseInterp] [GooseSemantics] go_gctx in
/-- The indices a `Ready` hands out are within the log (2026-10-18, D19b stage 5, `readyIdx`):
the unstable entries not yet handed out end at the last index, the committed log handed out
(`applying` long, then `ce`) is at most `committed` long. -/
theorem readyIdx_pure (ls : LogState) (d ce : List EntryM)
    (Hidx : LogIndicesOk ls.prev (ls.sents ++ ls.uents))
    (Hip : logOffset ls ≤ uint.Z ls.inprogress)
    (Hap : uint.Z ls.applying ≤ uint.Z ls.committed)
    (Hcm : uint.Z ls.committed ≤ uint.Z ls.prev.index' + (ls.sents.length : Int)
      + (ls.uents.length : Int))
    (Hdlen : d.length = (uint.Z ls.applying).toNat) (Hce : CeOk ls ce) :
    (∀ e0, (nextUnstable ls).head? = some e0 → uint.Z e0.Index' + ((nextUnstable ls).length : Int)
        ≤ uint.Z ls.prev.index' + (ls.sents.length : Int) + (ls.uents.length : Int) + 1) ∧
      ((d ++ ce).length : Int) ≤ uint.Z ls.prev.index' + (ls.sents.length : Int)
        + (ls.uents.length : Int) := by
  have Hapz := uint_Z_nonneg ls.applying
  refine ⟨fun e0 He0 => ?_, ?_⟩
  · unfold nextUnstable at He0 ⊢
    rw [List.head?_drop] at He0
    have Hk := (List.getElem?_eq_some_iff.mp He0).1
    have Hi := Hidx (ls.sents.length + (uint.Z ls.inprogress - logOffset ls).toNat) e0 (by
      rw [List.getElem?_append_right (by omega)]; simpa using He0)
    rw [List.length_drop]
    unfold logOffset at Hip
    push_cast at Hi ⊢
    omega
  · rw [List.length_append]
    cases Hl : ce.getLast? with
    | none =>
      rw [List.getLast?_eq_none_iff.mp Hl, List.length_nil, Hdlen]
      push_cast
      rw [Int.toNat_of_nonneg Hapz]; omega
    | some e =>
      have H := Hce e Hl
      rw [Hdlen]
      push_cast
      rw [Int.toNat_of_nonneg Hapz]; omega

/-- (U8 v2) `applying` is below `offsetInProgress` (`FlOk`), read out. -/
theorem ownRaftLog_applying_lt (l : Loc) (ls : LogState) :
    ⊢ ownRaftLog (GF := GF) l ls -∗
      ⌜uint.nat ls.applying < uint.nat ls.inprogress⌝ ∗ ownRaftLog l ls := by
  iintro H0
  iNamed H0
  isplitr
  · ipureintro
    have := Hfl.2.2.1
    have h1 := uint_nat_eq ls.applying; have h2 := uint_nat_eq ls.inprogress
    omega
  · iapply ownRaftLog_intro (sn := ls.sn) l lv lv.storage' σ _ _ ls rfl Hcm Hap Hidx Hnowrap Hstore
      Hoffset Happlied Hpapplied Hcommitted Hapg Hip Hipb Hpersist Happlying
      Hpaused Hasz Hamx Hstor Hpend Hfl Hsip Hsipn Hlent Hq Hprel Hsat Hfr rfl rfl rfl rfl rfl $$ Hl
      HisStorage HStorage Husnap Hpksn Hkcert Huents Huents_cap Hl_logger Hu_logger

/-- (U8 v2, 2026-10-29) **Certifying the terms of the entries `L`** at the indices `n + 1, …` past
the certified height `n` (`ownRaftLog_certify`, one by one): each at most `committed`, of the log's
term there once at or past the boundary. -/
theorem ownRaftLog_certify_list (l : Loc) (L : List EntryM) :
    ∀ (ls : LogState) (n : Nat), ls.dtk = n →
      ((n + L.length : Nat) : Int) ≤ uint.Z ls.committed →
      (∀ (k : Nat) (e : EntryM), L[k]? = some e →
        uint.Z ls.prev.index' ≤ ((n + k + 1 : Nat) : Int) →
        plogTermAt ls.prev (ls.sents ++ ls.uents) (W64 ((n + k + 1 : Nat) : Int)) = some e.Term') →
      ⊢ ownRaftLog (GF := GF) l ls ==∗
        ownRaftLog l { ls with dtk := n + L.length } ∗ dlvKeysAt ls.sn n L := by
  sorry -- PHASE1
  /- PHASE1-OLD
 by
  induction L with
  | nil =>
    intro ls n Hn _ _
    iintro H
    imodintro
    have : ({ ls with dtk := n + 0 } : LogState) = ls := by
      cases ls; simp only at Hn ⊢; rw [Hn]; rfl
    rw [this]
    iframe H
    iapply dlvKeysAt_nil
  | cons e L ih =>
    intro ls n Hn Hc Ht
    iintro H
    have Hc1 : ((n + 1 : Nat) : Int) ≤ uint.Z ls.committed := by
      simp only [List.length_cons] at Hc; omega
    imod ownRaftLog_certify l ls (n + 1) e.Term' (by omega) Hc1
      (fun hp => by have := Ht 0 e rfl (by simpa using hp); simpa using this) $$ H
      with ⟨H, #Hk⟩
    imod ih { ls with dtk := n + 1 } (n + 1) rfl
      (by simp only [List.length_cons] at Hc ⊢; omega)
      (fun k e' hk hp => by
        have := Ht (k + 1) e' (by simpa using hk) (by simp only at hp ⊢; omega)
        simp only at this ⊢
        rw [show n + 1 + k + 1 = n + (k + 1) + 1 by omega]; exact this) $$ H
      with ⟨H, #Hks⟩
    imodintro
    have : ({ ({ ls with dtk := n + 1 } : LogState) with dtk := n + 1 + L.length } : LogState) =
        { ls with dtk := n + (e :: L).length } := by
      simp only [List.length_cons]; congr 1; omega
    rw [this]
    iframe H
    unfold dlvKeysAt
    iapply BigSepL.bigSepL_cons.2
    isplitr
    · rw [show n + 0 + 1 = n + 1 by omega]; iexact Hk
    iunfold dlvKeysAt at Hks
    have hf : (fun j (x : EntryM) => iprop((n + 1 + j + 1) ↪[ls.sn.gd]□ x.Term' : IProp GF)) =
        (fun j (x : EntryM) => iprop((n + (j + 1) + 1) ↪[ls.sn.gd]□ x.Term' : IProp GF)) := by
      funext j x; rw [show n + 1 + j + 1 = n + (j + 1) + 1 by omega]
    rw [← hf]
    iexact Hks
  -/

/-- (D22 S-d3a; U8 v2) The log's part of a `Ready`'s hand-out (`readyOut`): the right to write the
batch, with the committed entries below it frozen (`ownRaftLog_handout`), or with a snapshot the
ranges above raft's frozen prefix and the snapshot handed out (`ownRaftLog_lend`). -/
theorem ownRaftLog_rdy_out (l : Loc) (ls : LogState) (es : List EntryM) (L : Option SnapLoan)
    (st : Storage) (Hunp : ls.unpersisted = []) (Hes : es = nextUnstable ls)
    (Hst : st = ls.storage) (Hn : L = none → ls.snap = none)
    (Hs : ∀ l, L = some l → ls.snap = some (snapId l.snap) ∧ ls.sip = false)
    (Hlt : ∀ l, L = some l → ls.lent = false) :
    ⊢ ownRaftLog (GF := GF) l ls ==∗ ownRaftLog l (rdyLog true L.isSome ls) ∗
      readyOut st ls.sn es L ∗
      (⌜L ≠ none⌝ ∨ storLog st (uint.nat ls.applying + 1) DFrac.discard (frozenRdy ls)) := by
  sorry -- PHASE1
  /- PHASE1-OLD
 by
  iintro Hlog
  cases L with
  | none =>
    imod ownRaftLog_handout _ _ Hunp (Hn rfl) $$ Hlog with ⟨Hlog, Happ, #Hfr⟩
    imodintro
    isplitl [Hlog]
    · iExactEq Hlog; rfl
    unfold readyOut
    rw [Hes, Hst]
    iframe Happ
    iright; iexact Hfr
  | some lo =>
    obtain ⟨Hsn, Hsip⟩ := Hs lo rfl
    icases ownRaftLog_snap_facts _ _ $$ Hlog with ⟨%Hf, Hlog⟩
    have Hpv : ls.prev = snapId lo.snap := (Hf.2.2.2 _ Hsn).1
    imod ownRaftLog_lend _ _ Hunp (by rw [Hsn]; simp) (Hlt lo rfl) Hsip $$ Hlog
      with ⟨Hlog, ⟨%k, %old, HO, Hend, %Hk⟩, #Hg⟩
    imodintro
    isplitl [Hlog]
    · iExactEq Hlog; rfl
    isplitl [HO Hend]
    · simp only [readyOut]
      rw [Hst]
      rw [Hpv] at Hk Hg
      iframe Hg
      iexists k, old
      iframe HO Hend
      ipureintro; exact Hk
    ileft; ipureintro; simp
  -/

/-- (D22 S-d3a) The pure facts of a computed `Ready`'s snapshot. -/
theorem rdSnapRel_facts (γ : RaftNames) (rs : RNState) (rd : Ready) (ce : List EntryM)
    (L : Option SnapLoan) (s : NState) :
    rdSnapRel (GF := GF) γ rs rd ce L s ⊢
      ⌜(L = none → rd.Snapshot' = null ∧ s.logst.snap = none) ∧
        (∀ l, L = some l → l.ptr = rd.Snapshot' ∧ SnapRdy rs ce l s)⌝ ∗ rdSnapRel γ rs rd ce L s := by
  cases L with
  | none =>
    simp only [rdSnapRel]
    iintro %H
    isplitr
    · ipureintro; exact ⟨(fun _ => H), (fun _ h => by cases h)⟩
    ipureintro; exact H
  | some l =>
    simp only [rdSnapRel]
    iintro ⟨Hs, #Hc, #Hd, %H⟩
    isplitr
    · ipureintro; exact ⟨(fun h => by cases h), (fun l' h => by cases h; exact H)⟩
    iframe Hs Hc Hd
    ipureintro; exact H

/-- (2026-10-26, D22 J6a; J7b's raft part) **A lent snapshot's id is the last of its committed
log**: the committed log up to the snapshot a `Ready` hands out (`l.dlv`) ends at the snapshot's id
(`plogLast base0 l.dlv = snapId l.snap`, so its last entry has the snapshot's term). The node's log
is at the pending snapshot (`LogStoreOk`: its base is the snapshot's id), its full prefix ends at
its base (`FullOk`) and is committed up to the commit index, at least the base's; the loan's
committed log has the snapshot's length, so it is that full prefix (`isCommitted_agree`). -/
theorem ownRawNodeReady_loanLast (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState)
    (rd : Ready) (ce es : List EntryM) (ms : List QMsg) (h : Bool) (l : SnapLoan) :
    ownRawNodeReady (GF := GF) γ rn id rs rd ce es ms h (some l) ⊢
      ⌜plogLast base0 l.dlv = snapId l.snap⌝ ∗ ownRawNodeReady γ rn id rs rd ce es ms h (some l) := by
  sorry -- PHASE1
  /- PHASE1-OLD
 by
  iintro H
  ihave %Hx : ⌜plogLast base0 l.dlv = snapId l.snap⌝ $$ [H]
  · iunfold ownRawNodeReady at H
    icases H with ⟨%s, %cf, %fp, %ds, %rnv, %sv, %hprev, H⟩
    iNamed H
    unfold rdSnapRel
    icases Hrdz with ⟨-, #Hcl, -, %Hr⟩
    obtain ⟨-, hsr⟩ := Hr
    have hsn : s.logst.snap = some (snapId l.snap) := hsr.1
    have hdl : l.dlv.length = (uint.Z l.snap.Metadata'.Index').toNat := hsr.2.2.2.2.2.2.2.1
    iunfold ownRaftPhysReady at Hphys
    iNamed Hphys
    icases ownRaftLog_pure s.log (rdyLog h (some l).isSome s.logst)
      (s.logst.prev = snapId l.snap ∧ uint.Z s.logst.prev.index' ≤ uint.Z s.logst.committed)
      (fun lv σ _ _ Hst _ Happ _ _ _ _ => by
        have e1 : (rdyLog h (some l).isSome s.logst).snap = s.logst.snap := by
          unfold rdyLog logHanded; split <;> simp
        have e2 : (rdyLog h (some l).isSome s.logst).prev = s.logst.prev := by
          unfold rdyLog logHanded; split <;> simp
        have e3 : (rdyLog h (some l).isSome s.logst).committed = s.logst.committed := by
          unfold rdyLog logHanded; split <;> simp
        rw [e1, hsn, e2] at Hst
        rw [e2, e3] at Happ
        exact ⟨Hst.1, Happ.1⟩) $$ Hlog with ⟨%Hpv, -⟩
    iunfold ownStepGhost at Hghost
    icases Hghost with ⟨Hg, -⟩
    icases ownRaftGhost_cmt γ id _ $$ Hg with ⟨%fp', %Hf', -, #Hc⟩
    have hb : (toPState (if h then { s with outbox := [] } else s)).base = snapId l.snap := by
      rw [← Hpv.1]; cases h <;> rfl
    have hcm : (toPState (if h then { s with outbox := [] } else s)).commit = s.logst.committed := by
      cases h <;> rfl
    rw [hb] at Hf'
    icases isCommitted_agree γ _ _ $$ Hcl Hc with %Hag
    ipureintro
    obtain ⟨Hfl, -, Hfl2⟩ := Hf'
    have hlen : (fp'.length : Int) = (l.dlv.length : Int) := by
      rw [Hfl, hdl]; simp only [snapId]
      have := uint_Z_nonneg l.snap.Metadata'.Index'; omega
    have hfp : fp' <+: cprefix fp' (toPState (if h then { s with outbox := [] } else s)) := by
      unfold cprefix
      rw [hcm, List.take_append, List.take_of_length_le]
      · exact List.prefix_append _ _
      · have := Hpv.2; rw [Hpv.1] at this
        simp only [snapId] at Hfl this
        omega
    have heq : fp' = l.dlv := by
      rcases Hag with h1 | h1
      · exact (List.prefix_of_prefix_length_le hfp h1 (by omega)).eq_of_length (by omega)
      · exact (hfp.trans h1).eq_of_length (by omega)
    rw [← heq]; exact Hfl2
  iframe H
  ipureintro; exact Hx
  -/

/-- The storage's hand-out for the entries a computed `Ready` hands out (2026-10-10): the
right to append them, ahead of `acceptReady` (`ownRaftLog_handout`). `node.go` runs it in
the atomic update of `readyc <- rd`, giving the right to the application with the `Ready`;
`acceptReady` takes the node after it. Since 2026-10-13 also the drain of the abstract
outbox (`Step.drain`, `ownRaftGhost_drain`), handing out with each message its read credit
(one for a `MsgReadIndex`). (D22 S-d3a, 2026-10-21) With a snapshot (`L`), the storage itself
(`ownRaftLog_lend`, `readyOut`). -/
theorem ownRawNodeReady_handout (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState)
    (rd : Ready) (ce es : List EntryM) (ms : List QMsg) (L : Option SnapLoan) :
    ⊢ ownRawNodeReady (GF := GF) γ rn id rs rd ce es ms false L ==∗
      ownRawNodeReady γ rn id rs rd ce es ms true L ∗ readyOut rs.storage rs.sn es L ∗
      -- (U8 v2) the committed entries below the batch, frozen; raft's certified terms of the
      -- committed log handed out
      (⌜L ≠ none⌝ ∨ ceFrozen rs.storage rs.delivered.length ce es) ∗
      dlvKeysAt rs.sn rs.delivered.length ((dlvAfter rs.delivered ce L).drop rs.delivered.length) ∗
      ([∗list] q ∈ ms, rdCred γ (if q.st.msg.Type' = MsgReadIndex then 1 else 0)) ∗
      -- (2026-10-19, D21 M6) and each proposal's tickets
      ([∗list] q ∈ ms, stTks γ q.st) ∗
      -- (2026-10-18, D19b stage 5) the indices handed out are within the log
      readyIdx γ rs.delivered ce es := by
  sorry -- PHASE1
  /- PHASE1-OLD
 by
  iintro H
  -- (U8 v2) a lent snapshot's committed log ends at it
  ihave %Hllast : ⌜∀ l, L = some l → plogLast base0 l.dlv = snapId l.snap⌝ $$ [H]
  · cases L with
    | none => ipureintro; intro l h; cases h
    | some l0 =>
      icases ownRawNodeReady_loanLast γ rn id rs rd ce es ms false l0 $$ H with ⟨%Hx, -⟩
      ipureintro; intro l h; cases h; exact Hx
  iunfold ownRawNodeReady at H
  icases H with ⟨%s, %c, %fp, %ds, %rnv, %sv, %hprev, H⟩
  iNamed H
  iunfold ownRaftPhysReady at Hphys
  icases Hphys with ⟨%rsl, %sl1, %sl2, %ms1, %ms2, Hphys⟩
  iNamed Hphys
  simp only [Bool.false_eq_true, ↓reduceIte]
  ihave Hlog : ownRaftLog s.log s.logst $$ [Hlog]
  · iExactEq Hlog; rfl
  -- (2026-10-18, D19b stage 5) the indices handed out, from the log and the ghost state
  icases ownRaftLog_pure _ _ (LogIndicesOk s.logst.prev (s.logst.sents ++ s.logst.uents) ∧
      uint.Z s.logst.prev.index' + (s.logst.sents.length : Int) + 1 ≤ uint.Z s.logst.inprogress ∧
      uint.Z s.logst.applying ≤ uint.Z s.logst.committed ∧
      uint.Z s.logst.committed ≤ uint.Z s.logst.prev.index' + (s.logst.sents.length : Int)
        + (s.logst.uents.length : Int) ∧
      (logOffset s.logst ≤ uint.Z s.logst.inprogress ∧
        uint.Z s.logst.inprogress ≤ logOffset s.logst + (s.logst.uents.length : Int)) ∧
      uint.Z s.logst.prev.index' ≤ uint.Z s.logst.committed ∧
      (s.logst.snap = none → uint.Z s.logst.prev.index' ≤ uint.Z s.logst.applied) ∧
      uint.Z s.logst.applied ≤ uint.Z s.logst.applying)
    (fun _ _ Hidx _ _ Hoff Hpc Hpa Hcm Hipb Happ =>
      ⟨Hidx, by omega, Happ.2, Hcm, by unfold logOffset; omega, Hpc.1, Hpa, Happ.1⟩) $$ Hlog
    with ⟨%Hlf, Hlog⟩
  obtain ⟨Hidx, Hoff, Hapc, Hcm, Hip, Hpc, Hpa0, Hapa⟩ := Hlf
  have Hri := readyIdx_pure s.logst rs.delivered ce Hidx (by unfold logOffset; omega) Hapc
    Hcm Hdlen Hceok
  icases ownRaftLog_applying_lt _ _ $$ Hlog with ⟨%Hai, Hlog⟩
  icases ownRaftLog_snap_facts _ _ $$ Hlog with ⟨%Hsf, Hlog⟩
  -- the storage: the right to append the batch, or (a snapshot) the storage itself
  icases rdSnapRel_facts γ rs rd ce L s $$ Hrdz with ⟨%Hrdp, Hrdz⟩
  have Hlt0 : ∀ l, L = some l → s.logst.lent = false := by
    intro l _
    have h1 := Hgh_unst.1.2.1.1
    rw [h1, Hloan.1.1, Hloan.2]; rfl
  have hA := uint_nat_eq s.logst.applying
  have hC := uint_nat_eq s.logst.committed
  have hP := uint_nat_eq s.logst.prev.index'
  have hI := uint_nat_eq s.logst.inprogress
  have Hdl : rs.delivered.length = uint.nat s.logst.applying := by rw [Hdlen]; rfl
  have Hpv : ∀ l, L = some l → s.logst.prev = snapId l.snap := fun l hl =>
    (Hsf.2.2.2 _ (Hrdp.2 l hl).2.1).1
  -- (U8 v2) the committed log handed out agrees with the log (`ownStepGhost_cmt_ents`)
  have Hcel : L = none → uint.nat s.logst.applying + ce.length ≤ uint.nat s.logst.committed := by
    intro _
    cases hc : ce.getLast? with
    | none => rw [List.getLast?_eq_none_iff.mp hc]; simp only [List.length_nil]; omega
    | some e => have := Hceok e hc; omega
  have Hpa : L = none → uint.nat s.logst.prev.index' ≤ uint.nat s.logst.applying := by
    intro h
    have := Hpa0 (Hrdp.1 h).2
    omega
  ihave %Hag : ⌜L = none → ∀ k e, (s.logst.sents ++ s.logst.uents)[k]? = some e →
      uint.nat s.logst.prev.index' + k < (rs.delivered ++ ce).length →
      (rs.delivered ++ ce)[uint.nat s.logst.prev.index' + k]? = some e⌝ $$ [Hghost]
  · cases L with
    | some _ => ipureintro; intro h; cases h
    | none =>
      icases ownStepGhost_cmt_ents γ _ c id s (rs.delivered ++ ce)
        (by rw [List.length_append, Hdl]; have := Hcel rfl; omega) $$ Hcommitted Hghost
        with ⟨%Hx, -⟩
      ipureintro; intro _; exact Hx
  -- (U8 v2) raft certifies the terms of the committed log handed out
  have HKlen : rs.delivered.length +
      ((dlvAfter rs.delivered ce L).drop rs.delivered.length).length =
      (dlvAfter rs.delivered ce L).length := by
    rw [List.length_drop]
    cases L with
    | none => simp only [dlvAfter, List.length_append]; omega
    | some l =>
      have := (Hrdp.2 l rfl).2.2.2.2.2.2.1.length_le
      simp only [dlvAfter]; omega
  have HKc : ((rs.delivered.length +
      ((dlvAfter rs.delivered ce L).drop rs.delivered.length).length : Nat) : Int) ≤
      uint.Z s.logst.committed := by
    rw [HKlen]
    cases L with
    | none => simp only [dlvAfter, List.length_append]; have := Hcel rfl; omega
    | some l =>
      have hsr := (Hrdp.2 l rfl).2
      have h1 : (l.dlv.length : Int) = uint.Z l.snap.Metadata'.Index' := by
        rw [hsr.2.2.2.2.2.2.2.1]; have := hsr.2.2.2.1; omega
      have h2 : uint.Z s.logst.prev.index' = uint.Z l.snap.Metadata'.Index' := by
        rw [Hpv l rfl]; rfl
      simp only [dlvAfter]; omega
  have HKt : ∀ (k : Nat) (e : EntryM),
      ((dlvAfter rs.delivered ce L).drop rs.delivered.length)[k]? = some e →
      uint.Z s.logst.prev.index' ≤ ((rs.delivered.length + k + 1 : Nat) : Int) →
      plogTermAt s.logst.prev (s.logst.sents ++ s.logst.uents)
        (W64 ((rs.delivered.length + k + 1 : Nat) : Int)) = some e.Term' := by
    intro k e hk hp
    cases L with
    | none =>
      simp only [dlvAfter, List.drop_left] at hk
      rw [Hdl]
      exact cmt_termAt s.logst rs.delivered ce Hdl (Hpa rfl) Hcm (Hcel rfl) (Hag rfl) k e hk
    | some l =>
      have hsr := (Hrdp.2 l rfl).2
      simp only [dlvAfter] at hk
      have hkl := (List.getElem?_eq_some_iff.1 hk).1
      rw [List.length_drop] at hkl
      have hdl' : (l.dlv.length : Int) = uint.Z l.snap.Metadata'.Index' := by
        rw [hsr.2.2.2.2.2.2.2.1]; have := hsr.2.2.2.1; omega
      have h2 : uint.Z s.logst.prev.index' = uint.Z l.snap.Metadata'.Index' := by
        rw [Hpv l rfl]; rfl
      -- the only index at or past the boundary is the snapshot's, the loan's last entry
      have hlast : rs.delivered.length + k + 1 = l.dlv.length := by omega
      have he : l.dlv.getLast? = some e := by
        rw [List.getElem?_drop] at hk
        rw [List.getLast?_eq_getElem?, show l.dlv.length - 1 = rs.delivered.length + k by omega]
        exact hk
      have hl := Hllast l rfl
      unfold plogLast at hl
      rw [he] at hl
      have ht : e.Term' = l.snap.Metadata'.Term' := by
        have := congrArg entryID.term' hl; simpa [entId, snapId] using this
      have hw : W64 ((rs.delivered.length + k + 1 : Nat) : Int) = s.logst.prev.index' := by
        rw [Hpv l rfl, hlast]; apply BitVec.eq_of_toNat_eq
        simp only [snapId]; word
      rw [hw, plogTermAt_base, Hpv l rfl, ht]; rfl
  imod ownRaftLog_certify_list s.log ((dlvAfter rs.delivered ce L).drop rs.delivered.length)
    s.logst rs.delivered.length Hsdt HKc HKt $$ Hlog with ⟨Hlog, #Hkeys⟩
  rw [HKlen]
  imod ownRaftLog_rdy_out s.log { s.logst with dtk := (dlvAfter rs.delivered ce L).length } es L
    rs.storage Hunp Hes Hstor.1
    (fun h => (Hrdp.1 h).2)
    (fun l h => ⟨(Hrdp.2 l h).2.1, (Hrdp.2 l h).2.2.1⟩) Hlt0 $$ Hlog
    with ⟨Hlog, Hout, #Hfrz⟩
  -- (U8 v2) the committed entries below the batch, frozen (`ceFrozen_pure`)
  ihave #Hcef : iprop(⌜L ≠ none⌝ ∨ ceFrozen rs.storage rs.delivered.length ce es) $$ []
  · cases L with
    | some _ => ileft; ipureintro; simp
    | none =>
      iright
      icases Hfrz with (%Hn | #Hfrz)
      · exact absurd rfl Hn
      obtain ⟨Hte, Hdisj⟩ := ceFrozen_pure s.logst rs.delivered ce Hdl (Hpa rfl) Hidx Hcm Hip
        (by omega) (Hcel rfl) (Hag rfl)
      unfold ceFrozen
      iexists min ce.length (frozenEnd s.logst - uint.nat s.logst.applying)
      isplitl
      · iapply storLog_sub _ _ 0 (min ce.length (frozenEnd s.logst - uint.nat s.logst.applying))
          _ _ _ (by rw [Hdl]; rfl) (by rw [List.drop_zero]; exact Hte) $$ Hfrz
      ipureintro
      rcases Hdisj with h | ⟨e0, he0, h⟩
      · left; exact h
      · right; refine ⟨e0, by rw [Hes]; exact he0, by rw [Hdl]; exact h⟩
  iunfold ownStepGhost at Hghost
  icases Hghost with ⟨Hghost, Hrest⟩
  ihave ⟨#Hlr, %HL⟩ := ownRaftGhost_lastRec γ id (toPState s) $$ Hghost
  imod ownRaftGhost_drain γ id (toPState s) [] (toPState s).outbox (List.Perm.refl _) $$ Hghost
    with ⟨Hghost, Hcr, Htk⟩
  ihave Htk := msgsTks_subperm γ _ (ms.filterMap (fun q => qProp q.st))
    (by rw [show propsOf (ms.filterMap (fun q => qProp q.st)) = ms.filterMap (fun q => qProp q.st)
        from ?_]
        · exact Hprc
        · unfold propsOf; rw [List.filter_eq_self]; intro a ha
          obtain ⟨q, -, hq⟩ := List.mem_filterMap.1 ha
          unfold qProp at hq; split at hq <;> simp at hq; subst hq
          simp [absMsg, absMsgFrom, Msg.mkV]) $$ Htk
  ihave Htk := msgsTks_qProp γ ms $$ Htk
  ihave Hrest := ghostRest_keep γ _ c id (s := s) (s' := { s with outbox := [] })
    rfl rfl rfl rfl rfl rfl rfl rfl $$ Hrest
  rw [show rdCount (toPState s).outbox - rdCount ([] : List Msg) =
      rdCountM (ms.map QMsg.st) + (rdCount s.outbox - rdCountM (ms.map QMsg.st)) by
    rw [show rdCount ([] : List Msg) = 0 from rfl]; show rdCount s.outbox - 0 = _; omega]
  icases (rdCred_split γ _ _).1 $$ Hcr with ⟨Hcr, -⟩
  ihave Hghost : ownStepGhost γ (rs.mode.toG ⟨rs.capplied, rs.cfg, fp, ds⟩) c id
      { s with outbox := [] } $$ [Hghost Hrest]
  · iunfold ownStepGhost
    iframe Hrest
    rw [show toPState { s with outbox := [] } = { toPState s with outbox := [] } from rfl]
    iexact Hghost
  imodintro
  isplitr [Hout Hcr Htk]
  · iunfold ownRawNodeReady
    iexists s, c, fp, ds, rnv, sv, hprev
    simp only [named, ↓reduceIte]
    iframe Hrn Hghost Hout Hsdrf Hsoft Hhard Hsteps Hsteps_cap Hcommitted Hstrecs Hrdsoft
      Hrdhard Hrdrs Hce Hce_cap Hents Hrdz Hsloc
    isplitl
    · iunfold ownRaftPhysReady
      iexists rsl, sl1, sl2, ms1, ms2
      simp only [named, ↓reduceIte]
      iframe Hf_id Hf_Term Hf_Vote Hf_readStates HreadStates HreadStates_cap Hf_raftLog
        Hf_state Hf_lead Hf_msgs Hf_msgsAA HmsgsAA HmsgsAA_cap Hself Hother Hundo Hlog Hclose Hscert
      ipureintro
      exact ⟨Houtbox, HmsgsAA_ok, Hout_term, Hgh_out, Hgh_unst, Hxf, Hmslen⟩
    ipureintro
    exact ⟨Hwf, Hin, Hasync, Hdlen, Hunp, Hsnap, Hloan, Htrm, Hstor, Hpvoff, Hrs_out, Hrs_unst,
      Hrs_clb, Hrnfl, Hceok, Hes, Hrdc, Hprc, Hnsout, Hsdt⟩
  isplitl [Hout]
  · rw [Hstor.2]; iexact Hout
  iframe Hcef
  isplitr
  · rw [Hstor.2]; iexact Hkeys
  isplitl [Hcr]
  · iapply rdCred_msgs γ ms $$ Hcr
  isplitl [Htk]
  · iexact Htk
  iunfold readyIdx
  iexists plogLastIndexZ (toPState s).base (toPState s).log
  iframe Hlr
  ipureintro
  have Hpl : plogLastIndexZ (toPState s).base (toPState s).log = uint.Z s.logst.prev.index'
      + (s.logst.sents.length : Int) + (s.logst.uents.length : Int) := by
    simp only [plogLastIndexZ, toPState, List.length_append]; push_cast; omega
  rw [Hpl] at HL ⊢
  rw [Hes]
  exact ⟨HL, Hri.1, Hri.2⟩
  -/

/-! ## A node with nothing new to hand out (2026-10-10)

`HasReady` returning `false` (`RawNode.HasReady.spec`) leaves the node as `ownRawNodeIdle`:
`ownRawNode` at a state with no queued message, no unstable entry still to be handed out,
no `ReadState` (2026-10-13), (D22 S-d3a) no snapshot to hand out (none pending, or the pending one
in progress), and so the lower bounds `outlb` and `unst` at their least
(`ownRawNodeIdle_facts`). Its use:
`node.go`'s `run` keeps a `Ready` it computed earlier armed when `HasReady` is `false`,
and may send it; by the lower bounds that `Ready` held nothing but committed entries still
the next ones, and possibly a stale `SoftState`/`HardState` (which only reset what
`HasReady` compares against), and `ownRawNodeIdle_ready` turns the node back into
`ownRawNodeReady` for it, so that `acceptReady` takes it. -/

/-- See the section header. (2026-10-16, stage R5: `ownRawNode`'s conjuncts as they are now:
`Hhard`, the queue `pendList`.) (D22 S-d3a, 2026-10-21: `ownRawNode`'s, a snapshot pending in
progress allowed.) -/
def ownRawNodeIdle (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) : IProp GF :=
  iprop(∃ (s : NState) (cf : CfgM) (fp : List EntryM) (ds : DecMap) (rnv : RawNode) (sv : SoftState)
      (hprev : HardStateM) (steps : List Loc),
  "Hrn" ∷ rawNodeOwn rn rnv ∗
  "Hphys" ∷ ownRaftPhysCV cf cf.voters rnv.raft' id s ∗
  "Hghost" ∷ ownStepGhost γ (rs.mode.toG ⟨rs.capplied, rs.cfg, fp, ds⟩) cf id s ∗
  "#Hsdrf" ∷ sdrOk rnv.raft' rs.mode ∗
  "%Hwf" ∷ ⌜NStateWf s⌝ ∗
  "%Hin" ∷ ⌜rs.mode = .static → id ∈ γ.reCfg⌝ ∗
  "%Hasync" ∷ ⌜rnv.asyncStorageWrites' = false⌝ ∗
  "#Hsoft" ∷ rnv.prevSoftSt' ↦□ sv ∗
  "#Hhard" ∷ prevHS γ rnv.prevHardSt' hprev rs.phs ∗
  "Hsteps" ∷ rnv.stepsOnAdvance' ↦* steps ∗
  "Hsteps_cap" ∷ ownSliceCap Loc rnv.stepsOnAdvance' (DFrac.own 1) ∗
  "Hpend" ∷ lentPend rs.slent (pendList γ id steps rs.steps) ∗
  "#Hdeliv" ∷ isCommitted γ rs.delivered ∗
  "#Hstrecs" ∷ ackInv γ rs s ∗
  "#Hloanc" ∷ loanCom γ rs.slent ∗
  "%Hdlen" ∷ ⌜rs.delivered.length = (uint.Z s.logst.applying).toNat⌝ ∗
  "%Hunp" ∷ ⌜rs.unpersisted = s.logst.unpersisted⌝ ∗
  "%Hsnap" ∷ ⌜rs.psnap = false ∧ rs.slent = none → s.logst.snap = none⌝ ∗
  "%Hstok" ∷ ⌜StepsOk s rs.steps⌝ ∗
  "%Htrm" ∷ ⌜rs.term = s.term⌝ ∗
  "%Hstor" ∷ ⌜rs.storage = s.logst.storage ∧ rs.sn = s.logst.sn⌝ ∗
  "%Hpvoff" ∷ ⌜RNPv rs fp s⌝ ∗
  "%Hrs_out" ∷ ⌜rs.outlb = s.gh.outlb⌝ ∗
  "%Hrs_unst" ∷ ⌜rs.unst = s.gh.unst⌝ ∗
  "%Hrs_clb" ∷ ⌜uint.Z rs.clb ≤ uint.Z s.logst.committed⌝ ∗
  "%Hrnfl" ∷ ⌜RNFl rs s⌝ ∗
  "%Hloan" ∷ ⌜LoanOk rs s⌝ ∗
  -- nothing new: no queued message, no unstable entry still to be handed out, no
  -- `ReadState` (2026-10-13), no snapshot to hand out (D22 S-d3a)
  "%Hidle" ∷ ⌜s.gh.outlb = 0 ∧ nextUnstable s.logst = [] ∧ s.rd.states = [] ∧
    (s.logst.snap = none ∨ s.logst.sip = true)⌝ ∗
  -- (2026-10-26, D22 J2, R-loc) as `ownRawNode`'s
  "#Hsloc" ∷ snapLocOk γ id s.logst.snap ∗
  -- (2026-10-28, stage U4a) as `ownRawNode`'s
  "%Hsdt" ∷ ⌜SdtTie rs s⌝)

theorem ownRawNodeIdle_intro (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState)
    (s : NState) (c : CfgM) (fp : List EntryM) {ds : DecMap} (rnv : RawNode) (sv : SoftState)
    (hprev : HardStateM) (steps : List Loc)
    (Hwf : NStateWf s) (Hin : rs.mode = .static → id ∈ γ.reCfg)
    (Hasync : rnv.asyncStorageWrites' = false)
    (Hdlen : rs.delivered.length = (uint.Z s.logst.applying).toNat)
    (Hunp : rs.unpersisted = s.logst.unpersisted)
    (Hsnap : rs.psnap = false ∧ rs.slent = none → s.logst.snap = none)
    (Hstok : StepsOk s rs.steps)
    (Htrm : rs.term = s.term) (Hstor : rs.storage = s.logst.storage ∧ rs.sn = s.logst.sn)
    (Hpvoff : RNPv rs fp s) (Hrs_out : rs.outlb = s.gh.outlb)
    (Hrs_unst : rs.unst = s.gh.unst) (Hrs_clb : uint.Z rs.clb ≤ uint.Z s.logst.committed)
    (Hrnfl : RNFl rs s) (Hloan : LoanOk rs s) (Hsdt : SdtTie rs s)
    (Hidle : s.gh.outlb = 0 ∧ nextUnstable s.logst = [] ∧ s.rd.states = [] ∧
      (s.logst.snap = none ∨ s.logst.sip = true)) :
    ⊢ rawNodeOwn rn rnv -∗ ownRaftPhysCV c c.voters rnv.raft' id s -∗
      ownStepGhost (GF := GF) γ (rs.mode.toG ⟨rs.capplied, rs.cfg, fp, ds⟩) c id s -∗
      sdrOk rnv.raft' rs.mode -∗
      rnv.prevSoftSt' ↦□ sv -∗ prevHS γ rnv.prevHardSt' hprev rs.phs -∗ rnv.stepsOnAdvance' ↦* steps -∗
      ownSliceCap Loc rnv.stepsOnAdvance' (DFrac.own 1) -∗
      lentPend rs.slent (pendList γ id steps rs.steps) -∗
      isCommitted γ rs.delivered -∗
      ackInv γ rs s -∗
      loanCom γ rs.slent -∗
      snapLocOk γ id s.logst.snap -∗
      ownRawNodeIdle γ rn id rs := by
  iintro Hrn Hphys Hghost #Hsdrf #Hsoft #Hhard Hsteps Hcap Hpend #Hdeliv #Hstrecs #Hloanc #Hsloc
  unfold ownRawNodeIdle
  iexists s, c, fp, ds, rnv, sv, hprev, steps
  simp only [named]
  iframe Hrn Hphys Hghost Hsdrf Hsoft Hhard Hsteps Hcap Hpend Hdeliv Hstrecs Hloanc Hsloc
  ipureintro
  exact ⟨Hwf, Hin, Hasync, Hdlen, Hunp, Hsnap, Hstok, Htrm, Hstor, Hpvoff, Hrs_out,
    Hrs_unst, Hrs_clb, Hrnfl, Hloan, Hidle, Hsdt⟩

theorem ownRawNodeIdle_ownRawNode (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) :
    ⊢ ownRawNodeIdle (GF := GF) γ rn id rs -∗ ownRawNode γ rn id rs := by
  iintro H
  iNamed H
  iapply ownRawNode_intro γ rn id rs s cf fp rnv sv hprev steps Hwf Hin Hasync Hdlen Hunp
    Hsnap Hstok Htrm Hstor Hpvoff Hrs_out Hrs_unst Hrs_clb Hrnfl Hloan
    Hsdt $$ Hrn Hphys Hghost Hsdrf Hsoft Hhard Hsteps Hsteps_cap Hpend Hdeliv Hstrecs Hloanc Hsloc

/-- What the client sees of an idle node: the lower bounds at their least, and the commit
index at most the committed log handed out (`applying`). (D22 S-d3a) With no loan: no snapshot
pending (`ownRawNodeIdle_nosnap`). -/
theorem ownRawNodeIdle_facts (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState)
    (Hsl : rs.slent = none) :
    ⊢ ownRawNodeIdle (GF := GF) γ rn id rs -∗
      ⌜rs.outlb = 0 ∧ rs.unst = false⌝ ∗ ownRawNodeIdle γ rn id rs := by
  sorry -- PHASE1
  /- PHASE1-OLD
 by
  iintro H
  iNamed H
  icases ownRaftPhysC_gh cf rnv.raft' id s $$ Hphys with ⟨%Hgh, Hphys⟩
  have Hsn : s.logst.snap = none := by
    rcases Hidle.2.2.2 with h | h
    · exact h
    · exact absurd (Hloan.2.1 Hsl).1 (Hgh.1.2.2.2.1 (.inl h))
  isplitr
  · ipureintro
    refine ⟨Hrs_out.trans Hidle.1, ?_⟩
    rw [Hrs_unst]
    cases Hu : s.gh.unst
    · rfl
    · rcases Hgh.1.1 Hu with H | H
      · exact absurd Hidle.2.1 H
      · exact absurd Hsn H
  iapply ownRawNodeIdle_intro γ rn id rs s cf fp rnv sv hprev steps Hwf Hin Hasync Hdlen Hunp
    Hsnap Hstok Htrm Hstor Hpvoff Hrs_out Hrs_unst Hrs_clb Hrnfl Hloan Hsdt Hidle
    $$ Hrn Hphys Hghost Hsdrf Hsoft Hhard Hsteps Hsteps_cap Hpend Hdeliv Hstrecs Hloanc Hsloc
  -/

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
    (Hrdz0 : rd.Snapshot' = null)
    (Hce_ok : ∀ e, ce.getLast? = some e → uint.Z e.Index' ≤ uint.Z rs.clb ∧
      uint.Z e.Index' = (rs.delivered.length : Int) + (ce.length : Int)) :
    ⊢ (⌜rd.SoftState' = null⌝ ∨ ∃ v : SoftState, rd.SoftState' ↦□ v) -∗
      hsOpt rd.HardState' hrd -∗
      -- (D22l) its witness (as `readyWithoutAccept` computed it)
      phsWit γ hrd -∗
      entsRO rd.CommittedEntries' ce -∗
      ownSliceCap Loc rd.CommittedEntries' (DFrac.own 1) -∗
      entsRO rd.Entries' [] -∗
      isCommitted γ (rs.delivered ++ ce) -∗ readStatesPts rd.ReadStates' sts -∗
      ownRawNodeIdle (GF := GF) γ rn id rs -∗ ownRawNodeReady γ rn id rs rd ce [] [] false := by
  sorry -- PHASE1
  /- PHASE1-OLD
 by
  iintro #Hrdsoft #Hrdh #Hrdw #Hce Hce_cap #Hents #Hcommitted #Hrsts H
  iNamed H
  have Hsl : rs.slent = none := Hloan.none_of_nil Hsteps0
  ihave Hpend := lentPend_none_elim Hsl _ $$ Hpend
  ihave %Hlen := BigSepL2.bigSepL2_length $$ Hpend
  have Hsteps_nil : steps = [] := by
    rw [Hsteps0] at Hlen; exact List.eq_nil_of_length_eq_zero Hlen
  subst Hsteps_nil
  icases ownRaftPhysC_gh cf rnv.raft' id s $$ Hphys with ⟨%Hgh, Hphys⟩
  have Hsn : s.logst.snap = none := by
    rcases Hidle.2.2.2 with h | h
    · exact h
    · exact absurd (Hloan.2.1 Hsl).1 (Hgh.1.2.2.2.1 (.inl h))
  icases ownRaftPhysC_nsOut γ _ cf rnv.raft' id s $$ Hphys Hghost with ⟨%Hnsout, Hphys, Hghost⟩
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
    ipureintro; intro _; exact Hidle.2.2.1
  icases outboxRel_split _ _ _ $$ Houtbox with ⟨%Hob, Hown1, Hown2⟩
  icases (qOwns_self_split id ms2).1 $$ Hown2 with ⟨Hself, Hoth⟩
  icases (qOwns_other_halves id ms2).2 $$ Hoth with ⟨Hhalf, Hother⟩
  ihave #Hrdhard : iprop(∃ hrd : HardStateM, hsOpt rd.HardState' hrd ∗ phsWit γ hrd) $$ []
  · iexists hrd; iframe Hrdh Hrdw
  ihave Hrdz : rdSnapRel γ rs rd ce none s $$ []
  · unfold rdSnapRel; ipureintro; exact ⟨Hrdz0, Hsn⟩
  iunfold ownRawNodeReady
  iexists s, cf, fp, ds, rnv, sv, hprev
  simp only [named, Bool.false_eq_true, ↓reduceIte]
  iframe Hrn Hghost Hsdrf Hout Hsoft Hhard Hsteps Hsteps_cap Hcommitted Hstrecs Hrdsoft Hrdrs
    Hce Hce_cap Hents Hrdhard Hrdz Hsloc
  isplitl
  · iunfold ownRaftPhysReady
    iexists rss, sl1, sl2, ms1, ms2
    simp only [named, Bool.false_eq_true, ↓reduceIte]
    iframe Hf_id Hf_Term Hf_Vote Hf_readStates HreadStates HreadStates_cap Hf_raftLog Hf_state
      Hf_lead Hf_msgs Hf_msgsAA HmsgsAA HmsgsAA_cap Hself Hother
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
    · ipureintro; exact Hxf
    isplitr
    · iexact Hscert
    isplitr
    · ipureintro; simp
    isplitl [Hmsgs Hmsgs_cap Hown1 Hhalf]
    · iintro - - -
      iframe Hmsgs Hmsgs_cap Hown1 Hhalf
    isplitl [Hlog]
    · iExactEq Hlog; rfl
    iintro %sl1' %sl2' %ms1' %ms2' %o %ls' %g %rs' %rd' HfTerm HfVote Hfrs Hrs' Hrsc %Hrd'
      Hflog Hfst Hfld Hfm Hm Hmc Hfma Hma Hmac Hob' %H1 %H2 %H3 %H4 %H5 %H6 %H7 #Hsc' Hl
    iapply Hclose $$ %sl1' %sl2' %ms1' %ms2' %o %ls' %g %rs' %rd' HfTerm HfVote Hfrs Hrs' Hrsc
      %Hrd' Hflog Hfst Hfld Hfm Hm Hmc Hfma Hma Hmac Hob' %H1 %H2 %H3 %H4 %H5 %H6 %H7 Hsc' Hl
  ipureintro
  refine ⟨Hwf, Hin, Hasync, Hdlen, Hunp0 ▸ Hunp.symm, Hsnap, ⟨Hloan, Hsl⟩, Htrm, Hstor, Hpvoff,
    Hrs_out, Hrs_unst, Hrs_clb,
    ⟨Hrnfl.1, Int.not_lt.1 fun h => by
      obtain ⟨_, _, Hm, -⟩ := Hrnfl.2 h; rw [Hsteps0] at Hm; simp at Hm⟩,
    fun e He => ?_, Hidle.2.1.symm, Nat.zero_le _, List.nil_subperm, Hnsout, Hsdt⟩
  obtain ⟨H1, H2⟩ := Hce_ok e He
  have Hne : ce ≠ [] := by intro h; subst h; simp at He
  have : 0 < ce.length := List.length_pos_iff.2 Hne
  have := uint_Z_nonneg s.logst.applying
  refine ⟨by omega, by omega, by omega⟩
  -/

/-- The `ReadState`s of the protocol state, each `readStateRaw` (2026-10-13): persistent,
copied out of `rdOwn`. -/
theorem ownRaftGhost_readStates (γ : RaftNames) (id : w64) (ps : PState) {md : Bool} :
    ⊢ ownRaftGhost (GF := GF) γ id ps md -∗ [∗list] st ∈ ps.rd.states, readStateRaw γ st := by
  unfold ownRaftGhost
  iintro ⟨%γv, %voted, %kl, H⟩
  iNamed H
  iunfold rdOwn at Hrd
  icases Hrd with ⟨%γl, %rqm, -, -, -, -, -, #Hst0, -⟩
  iexact Hst0

/-- The physical `ReadState`s are the protocol state's. -/
theorem toPState_rd_states (s : NState) : (toPState s).rd.states = s.rd.states := by
  by_cases h : s.role = .leader <;> simp [toPState, h, rdNL]

end rawnodeReady

end EtcdGrove
end Perennial
