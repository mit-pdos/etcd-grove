/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/internal/ledger/Spec.lean`, run `rabia-r1wake-1`.)

`rabia/internal/ledger`'s specs used by other packages (interface, stage 1a).

A `Slot` has two parts:
* the shared part, under `Slot.Lock` (the fix of R1, R2, R4, R3): its decision state and the
  received proposals and messages, abstractly a `SlotSt`; every method on it is logically
  atomic (`slotSt γ st`, half of a ghost variable; the lock's invariant holds the other half and
  the fields), so the consensus package keeps `slotSt γ st` in its own invariant;
* the executor's private part (`Phase`, `Round`, `MyProposal`, `MyBCMsgs`): `slotPriv s pv`,
  plain points-to's;
and two read-only fields: its `Queue` (a channel of capacity 10, made by `Reset`) and its `Term`
(0: no slot is reused, the stage's scope).
-/
module

public import Dsverify.GeneratedProof.rabia.internal.ledger
public import Dsverify.Proof.rabia.internal.message.SpecPure
public import Dsverify.Proof.rabia.internal.config.Spec
public import Perennial.Ghost.GhostVar
public import Perennial.Golang.Theory.Chan
public import Perennial.Golang.Theory.Chan.Idioms.Broadcast
public import Perennial.Proof.sync.Base
public import Dsverify.Proof.rabia.Core.PkgState
public import Dsverify.Proof.rabia.internal.ledger.Base



@[expose] public section

noncomputable section

namespace Perennial.rabia.internal.ledger

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode model rabia.internal.message
  rabia.internal.config

/-! ## The abstract state -/

/-- The counts of `0`s, `1`s and `?`s received at one round of a phase. -/
abbrev Counts := Nat × Nat × Nat

/-- A slot's shared state. `bc`/`bcT` are per phase (index): round 1's and round 2's counts and
totals; a phase beyond the list's end has none. `bcT` of phase 0, round 1 counts the proposals. -/
structure SlotSt where
  isDone : Bool
  hasRecvDec : Bool
  decision : ObjV
  props : List (ObjV × Nat)
  bc : List (Counts × Counts)
  bcT : List (Nat × Nat)
deriving DecidableEq, Inhabited

/-- The state of a slot after `Reset`, with phase arrays of length `L` (`Conf.LenBlockArray`). -/
def SlotSt.init (L : Nat) : SlotSt :=
  { isDone := false, hasRecvDec := false, decision := default, props := [],
    bc := List.replicate L ((0, 0, 0), (0, 0, 0)), bcT := List.replicate L (0, 0) }

/-- `RecvBCMsgs[phase][round-1]` (none beyond the arrays). -/
def SlotSt.counts (st : SlotSt) (phase round : Nat) : Counts :=
  match st.bc[phase]? with
  | some (c1, c2) => if round = 1 then c1 else c2
  | none => (0, 0, 0)

/-- `RecvBCMsgsT[phase][round-1]`. -/
def SlotSt.total (st : SlotSt) (phase round : Nat) : Nat :=
  match st.bcT[phase]? with
  | some (t1, t2) => if round = 1 then t1 else t2
  | none => 0

/-- `RecvBCMsgsMajV`/`MajT` of counts (ties go to 1). -/
def Counts.majV (c : Counts) : Nat := if c.1 > c.2.1 then 0 else 1
def Counts.majT (c : Counts) : Nat := if c.1 > c.2.1 then c.1 else c.2.1

/-- `PutRecvBCMsgs(phase, round, x)`. -/
def SlotSt.put (st : SlotSt) (phase round x : Nat) : SlotSt :=
  let bc := st.bc ++ List.replicate (phase + 1 - st.bc.length) ((0, 0, 0), (0, 0, 0))
  let bcT := st.bcT ++ List.replicate (phase + 1 - st.bcT.length) (0, 0)
  let inc (c : Counts) : Counts :=
    if x = 0 then (c.1 + 1, c.2.1, c.2.2) else if x = 1 then (c.1, c.2.1 + 1, c.2.2)
    else (c.1, c.2.1, c.2.2 + 1)
  { st with
    bc := bc.modify phase (fun p => if round = 1 then (inc p.1, p.2) else (p.1, inc p.2)),
    bcT := bcT.modify phase (fun p => if round = 1 then (p.1 + 1, p.2) else (p.1, p.2 + 1)) }

/-- `PutRecvProposals(p)`: a tally per proposal (by id), and the count of proposals. -/
def SlotSt.addProp (st : SlotSt) (o : ObjV) : SlotSt :=
  { st with
    props := if st.props.any (fun t => t.1.sameId o) then
        st.props.map (fun t => if t.1.sameId o then (t.1, t.2 + 1) else t)
      else st.props ++ [(o, 1)],
    bcT := (st.bcT ++ List.replicate (1 - st.bcT.length) (0, 0)).modify 0
      (fun p => (p.1 + 1, p.2)) }

/-- The order `SortRecvProposals` sorts by: more occurrences first, then the smaller id. -/
def tallyLt (a b : ObjV × Nat) : Bool :=
  decide (a.2 > b.2) || (decide (a.2 = b.2) &&
    (decide (a.1.proSeq.toNat < b.1.proSeq.toNat) ||
      (decide (a.1.proSeq = b.1.proSeq) && decide (a.1.proId.toNat < b.1.proId.toNat))))

/-- The tallies after `SortRecvProposals` (a permutation of them, sorted by `tallyLt`; the order
is total on tallies of distinct ids, so the result is determined). -/
def sortProps (ts : List (ObjV × Nat)) : List (ObjV × Nat) := ts.mergeSort tallyLt

/-! ## Representation and ghost state -/

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-! Internal (the prover's): the encodings of the abstract state, its well-formedness, the lock
invariant. -/

/-- The fields of an object, as a tuple (to encode it). -/
def objTup (o : ObjV) :=
  (o.proId, o.proSeq, o.svrSeq, o.isNull, o.cliIds, o.cliSeqs, o.commands)

theorem objTup_inj : Function.Injective objTup := by
  intro a b h
  cases a; cases b
  simp only [objTup, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  subst h1 h2 h3 h4 h5 h6 h7; rfl

instance : Pos.Countable SlotSt :=
  .ofInjective (fun st => Pos.Countable.encode (st.isDone, st.hasRecvDec, objTup st.decision,
      st.props.map (fun t => (objTup t.1, t.2)), st.bc, st.bcT))
    (by
      intro a b h
      have h := Pos.encode_inj h
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
      have hf : Function.Injective (fun t : ObjV × Nat => (objTup t.1, t.2)) := by
        intro x y hxy
        simp only [Prod.mk.injEq] at hxy
        exact Prod.ext (objTup_inj hxy.1) hxy.2
      have h4' := (List.map_inj_right (fun x y hxy => hf hxy)).1 h4
      have h3' := objTup_inj h3
      obtain ⟨⟩ := a; obtain ⟨⟩ := b
      simp only at h1 h2 h3' h4' h5 h6
      subst h1 h2 h3' h4' h5 h6; rfl)

/-- A count Go can hold in an `int` and compare as the natural number (`2^62`: the bound
`sort.Sort` needs on the tallies' length, which the proposals' total bounds). -/
abbrev cntOk (n : Nat) : Prop := n < 2 ^ 62

/-- The shared state's invariant facts: the tallies' ids are distinct (so the sort order is total
on them); every total fits (`cntOk`), and bounds the counts it totals (the tallies' counts and
their number by the proposals' total `total 0 1`, each count of `bc` by its total); the
per-phase arrays have the same length, at least one (`RecvBCMsgsT[0]` exists) and below `2^32`
(`uint32(len(..))` is the length). -/
def SlotSt.wf (st : SlotSt) : Prop :=
  (st.props.map Prod.fst).Pairwise (fun a b => a.sameId b = false) ∧
  (∀ t ∈ st.props, t.2 ≤ st.total 0 1) ∧ st.props.length ≤ st.total 0 1 ∧
  (∀ (p : Nat) (c : Counts × Counts) (t : Nat × Nat), st.bc[p]? = some c → st.bcT[p]? = some t →
    c.1.1 ≤ t.1 ∧ c.1.2.1 ≤ t.1 ∧ c.1.2.2 ≤ t.1 ∧ c.2.1 ≤ t.2 ∧ c.2.2.1 ≤ t.2 ∧ c.2.2.2 ≤ t.2) ∧
  (∀ t ∈ st.bcT, cntOk t.1 ∧ cntOk t.2) ∧
  1 ≤ st.bc.length ∧ st.bc.length = st.bcT.length ∧ st.bc.length < 2 ^ 32

/-- `RecvBCMsgs[p][r]`. -/
def encC (c : Counts) : GoArray w64 3 := array.mk 3 [W64 c.1, W64 c.2.1, W64 c.2.2]
/-- `RecvBCMsgs[p]`. -/
def encBC (p : Counts × Counts) : GoArray (GoArray w64 3) 2 := array.mk 2 [encC p.1, encC p.2]
/-- `RecvBCMsgsT[p]`. -/
def encT (t : Nat × Nat) : GoArray w64 2 := array.mk 2 [W64 t.1, W64 t.2]
/-- `MyBCMsgs[p]`. -/
def encMy (p : w32 × w32) : GoArray w32 2 := array.mk 2 [p.1, p.2]


/-- The client's half of the slot's shared state. -/
def slotSt (γ : GName) (st : SlotSt) : IProp GF := ghostVar γ (1 : Qp).half st

/-- The executor's private part of a slot. -/
structure PrivSt where
  phase : w32
  round : w32
  myProp : ObjV
  myBC : List (w32 × w32)

/-- `MyBCMsgs` holds `my` (entries beyond read as 0; at least `my`'s entries; fewer than
`2^32`). -/
def myRel (my : List (w32 × w32)) (vs : List (GoArray w32 2)) : Prop :=
  my.length ≤ vs.length ∧ vs.length < 2 ^ 32 ∧
    ∀ i (h : i < vs.length), vs[i] = encMy (my.getD i (0, 0))

/-- The `MyBCMsgs` field of slot `s` holds `my`. -/
def myRep (s : Loc) (my : List (w32 × w32)) : IProp GF :=
  iprop(∃ (msl : GoSlice) (vs : List (GoArray w32 2)),
    "Hmy" ∷ structFieldRef Slot go!"MyBCMsgs" s ↦ msl ∗
    "Hmysl" ∷ msl ↦* vs ∗
    "Hmycap" ∷ ownSliceCap (GoArray w32 2) msl (DFrac.own 1) ∗
    "%Hmyrel" ∷ ⌜myRel my vs⌝)

/-- The private fields of slot `s` hold `pv` (`MyBCMsgs` has at least the entries of `pv.myBC`,
entries beyond read as 0). -/
def slotPriv (s : Loc) (pv : PrivSt) : IProp GF :=
  iprop(∃ (mp : ConsensusObj),
    "Hph" ∷ structFieldRef Slot go!"Phase" s ↦ pv.phase ∗
    "Hrd" ∷ structFieldRef Slot go!"Round" s ↦ pv.round ∗
    "Hmp" ∷ structFieldRef Slot go!"MyProposal" s ↦ mp ∗
    "#Hmprep" ∷ objRep mp pv.myProp ∗
    "Hmy" ∷ myRep s pv.myBC)

/-- A received tally `t` holds `x`. -/
def tallyRep (t : Tally) (x : ObjV × Nat) : IProp GF :=
  iprop(objRep t.Proposal' x.1 ∗ ⌜t.Count' = W64 x.2⌝)

instance tallyRep_persistent (t : Tally) (x : ObjV × Nat) : Persistent (tallyRep (GF := GF) t x) :=
  by unfold tallyRep; infer_instance

/-- The Go tallies `tl` hold `xs` (index by index). Persistent. -/
def talliesRep (tl : List Tally) (xs : List (ObjV × Nat)) : IProp GF :=
  iprop(⌜tl.length = xs.length⌝ ∗
    □ (∀ (i : Nat) (t : Tally) (x : ObjV × Nat), ⌜tl[i]? = some t⌝ -∗ ⌜xs[i]? = some x⌝ -∗
      tallyRep t x))

instance talliesRep_persistent (tl : List Tally) (xs : List (ObjV × Nat)) :
    Persistent (talliesRep (GF := GF) tl xs) := by unfold talliesRep; infer_instance

/-- The decision field `dec` holds `st`'s decision, if the slot is done. -/
def decRep (dec : ConsensusObj) (done : Bool) (o : ObjV) : IProp GF :=
  if done then objRep dec o else iprop(True)

instance decRep_persistent (dec : ConsensusObj) (done : Bool) (o : ObjV) :
    Persistent (decRep (GF := GF) dec done o) := by
  unfold decRep; split <;> infer_instance

/-- The fields of slot `s` that `Lock` protects hold `st`. -/
def slotFields (s : Loc) (st : SlotSt) : IProp GF :=
  iprop(∃ (dec : ConsensusObj) (ps bs ts : GoSlice) (tl : List Tally),
    "Hdone" ∷ structFieldRef Slot go!"IsDone" s ↦ st.isDone ∗
    "Hrecv" ∷ structFieldRef Slot go!"HasRecvDec" s ↦ st.hasRecvDec ∗
    "Hdec" ∷ structFieldRef Slot go!"Decision" s ↦ dec ∗
    "#Hdecrep" ∷ decRep dec st.isDone st.decision ∗
    "Hps" ∷ structFieldRef Slot go!"RecvProposals" s ↦ ps ∗
    "Hpsl" ∷ ps ↦* tl ∗
    "Hpscap" ∷ ownSliceCap Tally ps (DFrac.own 1) ∗
    "#Htl" ∷ talliesRep tl st.props ∗
    "Hbs" ∷ structFieldRef Slot go!"RecvBCMsgs" s ↦ bs ∗
    "Hbsl" ∷ bs ↦* st.bc.map encBC ∗
    "Hbscap" ∷ ownSliceCap (GoArray (GoArray w64 3) 2) bs (DFrac.own 1) ∗
    "Hts" ∷ structFieldRef Slot go!"RecvBCMsgsT" s ↦ ts ∗
    "Htsl" ∷ ts ↦* st.bcT.map encT ∗
    "Htscap" ∷ ownSliceCap (GoArray w64 2) ts (DFrac.own 1))

/-- The `wake` field (R1-wake): `nil`, or an open channel that nothing is sent on (Perennial's
broadcast idiom, still `Pending`, broadcasting nothing: `True`). Only the lock's holder closes it
(`wakeWaiters`, which needs the `Pending` token and leaves the field `nil`), so a stored channel
is closed at most once. `done = false` records that a done slot has no wake channel (true of the
code; the safety proofs do not use it: that a waiter is woken is liveness, out of scope). -/
def wakeRep (s : Loc) (done : Bool) : IProp GF :=
  iprop(∃ w : GoChan, structFieldRef Slot go!"wake" s ↦ w ∗
    (⌜w = chan.nil⌝ ∨ (⌜done = false⌝ ∗ ∃ γw : ChanNames, ownBroadcastChan w γw iprop(True) .Pending)))

/-- The lock's invariant: the `wake` field (`wakeRep`), the protected fields hold some
well-formed `st`, and the other half of `γ` holds it. -/
def slotInv (s : Loc) (γ : GName) : IProp GF :=
  iprop(∃ st : SlotSt, "Hwk" ∷ wakeRep s st.isDone ∗ "Hf" ∷ slotFields s st ∗
    "Hγ" ∷ ghostVar γ (1 : Qp).half st ∗ "%Hwf" ∷ ⌜st.wf⌝)

/-- Slot `s`: its lock with its invariant (the shared fields and the other half of `γ`), its
queue `q` and term 0 (read-only). Persistent. -/
def isSlot (s : Loc) (γ : GName) (q : GoChan) : IProp GF :=
  iprop(structFieldRef Slot go!"Queue" s ↦□ q ∗ structFieldRef Slot go!"Term" s ↦□ (W32 0) ∗
    sync.isMutex (structFieldRef Slot go!"Lock" s) (slotInv s γ))

instance isSlot_persistent (s : Loc) (γ : GName) (q : GoChan) :
    Persistent (isSlot (GF := GF) s γ q) := by
  unfold isSlot; infer_instance

/-- The queue made by `Reset`: a fresh channel of capacity 10 (`ChanState.Buffered []`), with
the channel's resources for whoever sets up its protocol (the consensus package). -/
def queueFresh (q : GoChan) : IProp GF :=
  iprop(∃ γc : ChanNames, isChan q γc message.Msg ∗ ⌜γc.chanCap = W64 10⌝ ∗
    ownChan γc message.Msg (ChanState.Buffered []))

end defs

/-! ## The specs -/

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem : rabia.internal.ledger.Assumptions]

/-- `s.Reset()` on a zero slot (`&ledger.Slot{}`), then the lock's invariant allocated: the slot,
its initial state, the executor's part, its fresh queue. -/
abbrev Slot.Reset.spec : Prop :=
  ∀ (cf : RCfg) (s : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.ledger ∗ confRO cf ∗
      s ↦ (zeroValDef : Slot) }}
    (App (Val (s @!! go.GoType.PointerType Slot.ty @!! go!"Reset")) (Val #()))
  {{ RET #(); |={⊤}=> ∃ γ q, isSlot s γ q ∗ slotSt γ (SlotSt.init cf.blockLen) ∗
      slotPriv s { phase := 0, round := 0, myProp := default, myBC := [] } ∗ queueFresh q }}

/-- `s.SetDecision(dec)`: the slot is done with decision `o`. -/
abbrev Slot.SetDecision.spec : Prop :=
  ∀ (s : Loc) (γ : GName) (q : GoChan) (v : ConsensusObj) (o : ObjV),
  ⊢ isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.ledger -∗ isSlot s γ q -∗ objRep v o -∗
    <<{ ∀∀ st, slotSt γ st }>>
      (App (Val (s @!! go.GoType.PointerType Slot.ty @!! go!"SetDecision")) (Val #v)) @ ∅
    <<{ slotSt γ { st with isDone := true, decision := o } | RET #(); True }>>

/-- `s.GetDecision()`: the decision and whether the slot is done. -/
abbrev Slot.GetDecision.spec : Prop :=
  ∀ (s : Loc) (γ : GName) (q : GoChan),
  ⊢ isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.ledger -∗ isSlot s γ q -∗
    <<{ ∀∀ st, slotSt γ st }>>
      (App (Val (s @!! go.GoType.PointerType Slot.ty @!! go!"GetDecision")) (Val #())) @ ∅
    <<{ slotSt γ st | (v : ConsensusObj), RET (PairV #v #st.isDone);
        if st.isDone then objRep v st.decision else True }>>

/-- `s.GetDecisionOrWake()` (R1-wake): the decision and whether the slot is done, as
`GetDecision`; if it is not done, also a channel `w` that is closed when the slot's decision state
changes: a receive on it may block, or return once it is closed, and carries nothing (`True`). -/
abbrev Slot.GetDecisionOrWake.spec : Prop :=
  ∀ (s : Loc) (γ : GName) (q : GoChan),
  ⊢ isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.ledger -∗ isSlot s γ q -∗
    <<{ ∀∀ st, slotSt γ st }>>
      (App (Val (s @!! go.GoType.PointerType Slot.ty @!! go!"GetDecisionOrWake")) (Val #())) @ ∅
    <<{ slotSt γ st | (v : ConsensusObj) (w : GoChan), RET (PairV (PairV #v #st.isDone) #w);
        if st.isDone then objRep v st.decision
        else ∃ γw : ChanNames, ownBroadcastChan w γw iprop(True) .Unknown }>>

/-- `s.GetIsDone()`. -/
abbrev Slot.GetIsDone.spec : Prop :=
  ∀ (s : Loc) (γ : GName) (q : GoChan),
  ⊢ isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.ledger -∗ isSlot s γ q -∗
    <<{ ∀∀ st, slotSt γ st }>>
      (App (Val (s @!! go.GoType.PointerType Slot.ty @!! go!"GetIsDone")) (Val #())) @ ∅
    <<{ slotSt γ st | RET #st.isDone; True }>>

/-- `s.GetHasRecvDec()`. -/
abbrev Slot.GetHasRecvDec.spec : Prop :=
  ∀ (s : Loc) (γ : GName) (q : GoChan),
  ⊢ isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.ledger -∗ isSlot s γ q -∗
    <<{ ∀∀ st, slotSt γ st }>>
      (App (Val (s @!! go.GoType.PointerType Slot.ty @!! go!"GetHasRecvDec")) (Val #())) @ ∅
    <<{ slotSt γ st | RET #st.hasRecvDec; True }>>

/-- `s.SetHasRecvDec()`. -/
abbrev Slot.SetHasRecvDec.spec : Prop :=
  ∀ (s : Loc) (γ : GName) (q : GoChan),
  ⊢ isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.ledger -∗ isSlot s γ q -∗
    <<{ ∀∀ st, slotSt γ st }>>
      (App (Val (s @!! go.GoType.PointerType Slot.ty @!! go!"SetHasRecvDec")) (Val #())) @ ∅
    <<{ slotSt γ { st with hasRecvDec := true } | RET #(); True }>>

/-- `s.PutRecvProposals(p)`. -/
abbrev Slot.PutRecvProposals.spec : Prop :=
  ∀ (s : Loc) (γ : GName) (q : GoChan) (v : ConsensusObj) (o : ObjV),
  ⊢ isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.ledger -∗ isSlot s γ q -∗ objRep v o -∗
    <<{ ∀∀ st, slotSt γ st ∗ ⌜st.total 0 1 + 1 < 2 ^ 62⌝ }>>
      (App (Val (s @!! go.GoType.PointerType Slot.ty @!! go!"PutRecvProposals")) (Val #v)) @ ∅
    <<{ slotSt γ (st.addProp o) | RET #(); True }>>

/-- `s.RecvProposalsMajV()`: sorts the tallies; returns the first's proposal. -/
abbrev Slot.RecvProposalsMajV.spec : Prop :=
  ∀ (s : Loc) (γ : GName) (q : GoChan),
  ⊢ isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.ledger -∗ isSlot s γ q -∗
    <<{ ∀∀ st, slotSt γ st ∗ ⌜st.props ≠ []⌝ }>>
      (App (Val (s @!! go.GoType.PointerType Slot.ty @!! go!"RecvProposalsMajV")) (Val #())) @ ∅
    <<{ slotSt γ { st with props := sortProps st.props } | (v : ConsensusObj), RET #v;
        objRep v ((sortProps st.props).head?.map (·.1)).get! }>>

/-- `s.RecvProposalsMajT()`: sorts the tallies; returns the first's count. -/
abbrev Slot.RecvProposalsMajT.spec : Prop :=
  ∀ (s : Loc) (γ : GName) (q : GoChan),
  ⊢ isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.ledger -∗ isSlot s γ q -∗
    <<{ ∀∀ st, slotSt γ st ∗ ⌜st.props ≠ []⌝ }>>
      (App (Val (s @!! go.GoType.PointerType Slot.ty @!! go!"RecvProposalsMajT")) (Val #())) @ ∅
    <<{ slotSt γ { st with props := sortProps st.props } |
        RET #(W64 (((sortProps st.props).head?.map (·.2)).getD 0 : Nat)); True }>>

/-- `s.PutRecvBCMsgs(phase, round, x)` (`round` 1 or 2, `x` 0, 1 or 2). -/
abbrev Slot.PutRecvBCMsgs.spec : Prop :=
  ∀ (s : Loc) (γ : GName) (q : GoChan) (phase round x : w32),
  (round = 1 ∨ round = 2) → x.toNat ≤ 2 →
  ⊢ isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.ledger -∗ isSlot s γ q -∗
    <<{ ∀∀ st, slotSt γ st ∗ ⌜st.total phase.toNat round.toNat + 1 < 2 ^ 62⌝ }>>
      (App (App (App (Val (s @!! go.GoType.PointerType Slot.ty @!! go!"PutRecvBCMsgs"))
        (Val #phase)) (Val #round)) (Val #x)) @ ∅
    <<{ slotSt γ (st.put phase.toNat round.toNat x.toNat) | RET #(); True }>>

/-- `s.RecvBCMsgsMajV(phase, round)`. -/
abbrev Slot.RecvBCMsgsMajV.spec : Prop :=
  ∀ (s : Loc) (γ : GName) (q : GoChan) (phase round : w32),
  (round = 1 ∨ round = 2) →
  ⊢ isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.ledger -∗ isSlot s γ q -∗
    <<{ ∀∀ st, slotSt γ st }>>
      (App (App (Val (s @!! go.GoType.PointerType Slot.ty @!! go!"RecvBCMsgsMajV"))
        (Val #phase)) (Val #round)) @ ∅
    <<{ slotSt γ st | RET #(W32 ((st.counts phase.toNat round.toNat).majV : Nat)); True }>>

/-- `s.RecvBCMsgsMajT(phase, round)`. -/
abbrev Slot.RecvBCMsgsMajT.spec : Prop :=
  ∀ (s : Loc) (γ : GName) (q : GoChan) (phase round : w32),
  (round = 1 ∨ round = 2) →
  ⊢ isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.ledger -∗ isSlot s γ q -∗
    <<{ ∀∀ st, slotSt γ st }>>
      (App (App (Val (s @!! go.GoType.PointerType Slot.ty @!! go!"RecvBCMsgsMajT"))
        (Val #phase)) (Val #round)) @ ∅
    <<{ slotSt γ st | RET #(W64 ((st.counts phase.toNat round.toNat).majT : Nat)); True }>>

/-- `s.HasEnoughMsg(phase, round)`: at least `n - f` messages. -/
abbrev Slot.HasEnoughMsg.spec : Prop :=
  ∀ (cf : RCfg) (s : Loc) (γ : GName) (q : GoChan) (phase round : w32),
  (round = 1 ∨ round = 2) →
  ⊢ isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.ledger -∗ isSlot s γ q -∗ confRO cf -∗
    <<{ ∀∀ st, slotSt γ st }>>
      (App (App (Val (s @!! go.GoType.PointerType Slot.ty @!! go!"HasEnoughMsg"))
        (Val #phase)) (Val #round)) @ ∅
    <<{ slotSt γ st | RET #(decide (st.total phase.toNat round.toNat ≥ cf.q)); True }>>

/-- The executor's part: `SetMyProposal`, `GetMyProposal`, `SetMyBCMsgs`, `GetMyBCMsgs`,
`IncrPhaseDecrRound`, and the fields `Phase`, `Round` (loaded and stored directly by the
consensus package: `slotPriv` gives their points-to's by a law, `slotPriv_fields`). -/
abbrev Slot.SetMyProposal.spec : Prop :=
  ∀ (s : Loc) (pv : PrivSt) (v : ConsensusObj) (o : ObjV),
  {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.ledger ∗ slotPriv s pv ∗ objRep v o }}
    (App (Val (s @!! go.GoType.PointerType Slot.ty @!! go!"SetMyProposal")) (Val #v))
  {{ RET #(); slotPriv s { pv with myProp := o } }}

abbrev Slot.GetMyProposal.spec : Prop :=
  ∀ (s : Loc) (pv : PrivSt),
  {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.ledger ∗ slotPriv s pv }}
    (App (Val (s @!! go.GoType.PointerType Slot.ty @!! go!"GetMyProposal")) (Val #()))
  {{ (v : ConsensusObj), RET #v; slotPriv s pv ∗ objRep v pv.myProp }}

/-- `pv.myBC`'s entry of `phase`, `round` (0 beyond). -/
def PrivSt.my (pv : PrivSt) (phase round : Nat) : w32 :=
  match pv.myBC[phase]? with
  | some (a, b) => if round = 1 then a else b
  | none => 0

def PrivSt.setMy (pv : PrivSt) (phase round : Nat) (x : w32) : PrivSt :=
  let l := pv.myBC ++ List.replicate (phase + 1 - pv.myBC.length) (0, 0)
  { pv with myBC := l.modify phase (fun p => if round = 1 then (x, p.2) else (p.1, x)) }

abbrev Slot.SetMyBCMsgs.spec : Prop :=
  ∀ (s : Loc) (pv : PrivSt) (phase round x : w32), (round = 1 ∨ round = 2) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.ledger ∗ slotPriv s pv }}
    (App (App (App (Val (s @!! go.GoType.PointerType Slot.ty @!! go!"SetMyBCMsgs"))
      (Val #phase)) (Val #round)) (Val #x))
  {{ RET #(); slotPriv s (pv.setMy phase.toNat round.toNat x) }}

/-- `GetMyBCMsgs(phase, round)` of an entry that was set (the slice holds `phase`). -/
abbrev Slot.GetMyBCMsgs.spec : Prop :=
  ∀ (s : Loc) (pv : PrivSt) (phase round : w32), (round = 1 ∨ round = 2) →
    phase.toNat < pv.myBC.length →
  {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.ledger ∗ slotPriv s pv }}
    (App (App (Val (s @!! go.GoType.PointerType Slot.ty @!! go!"GetMyBCMsgs"))
      (Val #phase)) (Val #round))
  {{ RET #(pv.my phase.toNat round.toNat); slotPriv s pv }}

abbrev Slot.IncrPhaseDecrRound.spec : Prop :=
  ∀ (s : Loc) (pv : PrivSt),
  {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.ledger ∗ slotPriv s pv }}
    (App (Val (s @!! go.GoType.PointerType Slot.ty @!! go!"IncrPhaseDecrRound")) (Val #()))
  {{ RET #(); slotPriv s { pv with phase := pv.phase + 1, round := pv.round - 1 } }}

/-- The laws of the representation (statements; proved in Prove): the private part gives the
fields `Phase`, `Round` (loaded and stored directly) and `MyProposal` (read directly by `epilogue`
and `putBackMyProposal`); a slot gives its queue and term. -/
theorem slotPriv_fields (s : Loc) (pv : PrivSt) :
    slotPriv (GF := GF) s pv ⊣⊢
      (structFieldRef Slot go!"Phase" s ↦ pv.phase ∗ structFieldRef Slot go!"Round" s ↦ pv.round ∗
        (∃ v, structFieldRef Slot go!"MyProposal" s ↦ v ∗ objRep v pv.myProp) ∗
        ∃ rest : IProp GF, rest ∗
          ∀ ph rd (v : ConsensusObj), (structFieldRef Slot go!"Phase" s ↦ ph ∗
            structFieldRef Slot go!"Round" s ↦ rd ∗ structFieldRef Slot go!"MyProposal" s ↦ v ∗
            objRep v pv.myProp ∗ rest) -∗
            slotPriv s { pv with phase := ph, round := rd }) := by
  constructor
  · unfold slotPriv
    iintro H
    iNamed H
    iframe Hph Hrd
    isplitl [Hmp]
    · iexists mp; iframe Hmp Hmprep
    iexists (myRep s pv.myBC)
    iframe Hmy
    iintro %ph %rd %v ⟨Hph, Hrd, Hmp, #Hrep, Hmy⟩
    iexists v
    iframe Hph Hrd Hmp Hrep Hmy
  · iintro ⟨Hph, Hrd, ⟨%v, Hmp, #Hrep⟩, %rest, Hrest, Hw⟩
    iapply Hw $$ %pv.phase %pv.round %v
    iframe Hph Hrd Hmp Hrep Hrest

theorem isSlot_queue (s : Loc) (γ : GName) (q : GoChan) :
    isSlot (GF := GF) s γ q ⊢ structFieldRef Slot go!"Queue" s ↦□ q ∗
      structFieldRef Slot go!"Term" s ↦□ (W32 0) := by
  unfold isSlot
  iintro ⟨#Hq, #Ht, -⟩
  isplit
  · iexact Hq
  · iexact Ht

end spec

end Perennial.rabia.internal.ledger
