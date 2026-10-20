/-
The tracker's epoch with a witness (2026-10-19, witness support, `notes/raft-witness.md`): a
model of `tracker.Epoch` -- the leader's subterm and, per half of the configuration, its
replication set -- its representation predicate, and what the epoch functions compute
(`ResetReplicationSet`, `ChangeReplicationSet`, `OneLessThanQuorumInReplicationSet`).

The model, per half `i` (`RSM`): the half's witness in the replication set (`wit`, `0` when the
half has none), the excluded voter (`excl`: the witness when the leader has every regular voter;
a regular voter it considers down otherwise) and the replication set's voters other than the
witness (`nwv`, `NonWitnessVoters`: what the leader counts acknowledgements in and what it sends
the witness). `RSWF` is the invariant the functions keep: `nwv` is the half's voters but `wit`
and `excl`. The protocol's names for half 0 (`Protocol/StepC.lean`, branch raft-witness-w2):
`wit = c.wit`, `excl = exclOf c s`, `nwv = rsSet c s`.
-/
module

public import Proof.go_etcd_io.raft.v3.Defs

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode GMap go_etcd_io.raft.v3

/-- One half's replication set (`tracker.ReplicationSet`). -/
structure RSM where
  /-- `Witness`: the half's witness, `0` if none -/
  wit : w64
  /-- `Excluded`: the voter outside the replication set (`0` with no witness) -/
  excl : w64
  /-- `NonWitnessVoters` -/
  nwv : GSet w64

/-- The epoch (`tracker.Epoch`): the subterm and the two halves' replication sets. -/
structure EpochM where
  sub : w64
  rs0 : RSM
  rs1 : RSM

/-- A half with no witness, as a zero `ReplicationSet` holds it (nil voter map). -/
def RSM.bare : RSM := ⟨W64 0, W64 0, ∅⟩

/-- The epoch of a configuration without a witness at subterm `sub`. -/
def EpochM.bare (sub : w64) : EpochM := ⟨sub, RSM.bare, RSM.bare⟩

/-- `Epoch.HasWitness`. -/
def EpochM.hasWit (em : EpochM) : Bool :=
  decide (em.rs0.wit ≠ W64 0 ∨ em.rs1.wit ≠ W64 0)

/-- `ReplicateToWitness`'s per-half answer: the half has a witness, in its replication set. -/
def RSM.rep (r : RSM) : Bool := decide (r.wit ≠ W64 0 ∧ r.excl ≠ r.wit)

/-- A half's replication set, for the half's voters `V` and the configuration's witness `w` of
that half (`Config.Witnesses[i]`): the witness if it is a voter of the half, the excluded voter
the witness or one of the half's regular voters, and the non-witness voters the half's voters
but those two. -/
def RSWF (V : GSet w64) (w : w64) (r : RSM) : Prop :=
  r.wit = (if w ∈ V then w else W64 0) ∧
  (r.excl = r.wit ∨ (r.excl ∈ V ∧ r.excl ≠ r.wit ∧ r.wit ≠ W64 0)) ∧
  r.nwv = V \ ({[r.wit]} ∪ {[r.excl]})

/-- The epoch of a configuration (voters `V0`, `V1`, witnesses `w0`, `w1`): bare with no
witness (`ResetReplicationSet`'s early return, `MakeProgressTracker`), else both halves' sets
well formed. -/
def EpochWF (V0 V1 : GSet w64) (w0 w1 : w64) (em : EpochM) : Prop :=
  (w0 = W64 0 ∧ w1 = W64 0 ∧ em.rs0 = RSM.bare ∧ em.rs1 = RSM.bare) ∨
  (¬ (w0 = W64 0 ∧ w1 = W64 0) ∧ RSWF V0 w0 em.rs0 ∧ RSWF V1 w1 em.rs1)

/-- What `ResetReplicationSet` builds for a half: the witness excluded, every other voter in. -/
def rsReset (V : GSet w64) (w : w64) : RSM :=
  let x := if w ∈ V then w else W64 0
  ⟨x, x, V \ {[w]}⟩

/-- `ResetReplicationSet` at subterm `sub'` (`0`, or the old one plus one). -/
def resetEpoch (V0 V1 : GSet w64) (w0 w1 : w64) (sub' : w64) : EpochM :=
  if w0 = W64 0 ∧ w1 = W64 0 then EpochM.bare sub'
  else ⟨sub', rsReset V0 w0, rsReset V1 w1⟩

/-- A replication-set change (`ChangeReplicationSet`'s result when it changes the epoch): the
next subterm, the same witnesses, and both halves well formed. Which voter the leader excludes
is not specified (it reads the peers' `RecentActive`, which the `Progress` model leaves out):
the protocol's `newSub` allows any. -/
def ChangeEpochOk (V0 V1 : GSet w64) (w0 w1 : w64) (em em' : EpochM) : Prop :=
  em'.sub = em.sub + W64 1 ∧ EpochWF V0 V1 w0 w1 em' ∧
  em'.rs0.wit = em.rs0.wit ∧ em'.rs1.wit = em.rs1.wit

/-- The acknowledgements an indexer scoped to `S` reports (`scopedAckIndexer`): the inner
indexer's for ids of `S`, none for the others. -/
def scopedAcked (S : GSet w64) (acked : w64 → Option w64) (id : w64) : Option w64 :=
  if id ∈ S then acked id else none

theorem rsReset_wf (V : GSet w64) (w : w64) (H0 : W64 0 ∉ V) : RSWF V w (rsReset V w) := by
  unfold RSWF rsReset
  refine ⟨rfl, Or.inl rfl, ?_⟩
  simp only
  split
  · apply set_eq; intro k; simp only [elem_of_difference, elem_of_union, elem_of_singleton, or_self]
  · rename_i hw
    apply set_eq; intro k; simp only [elem_of_difference, elem_of_union, elem_of_singleton, or_self]
    constructor
    · rintro ⟨hk, _⟩; exact ⟨hk, fun h => by subst h; exact H0 hk⟩
    · rintro ⟨hk, _⟩; exact ⟨hk, fun h => by subst h; exact hw hk⟩

theorem resetEpoch_wf (V0 V1 : GSet w64) (w0 w1 sub' : w64) (H0 : W64 0 ∉ V0)
    (H1 : W64 0 ∉ V1) : EpochWF V0 V1 w0 w1 (resetEpoch V0 V1 w0 w1 sub') := by
  unfold EpochWF resetEpoch
  split
  · rename_i h; exact Or.inl ⟨h.1, h.2, rfl, rfl⟩
  · rename_i h; exact Or.inr ⟨h, rsReset_wf V0 w0 H0, rsReset_wf V1 w1 H1⟩

theorem resetEpoch_sub (V0 V1 : GSet w64) (w0 w1 sub' : w64) :
    (resetEpoch V0 V1 w0 w1 sub').sub = sub' := by
  unfold resetEpoch; split <;> rfl

/-- With no witness, the reset epoch is bare. -/
theorem resetEpoch_nw (V0 V1 : GSet w64) (sub' : w64) :
    resetEpoch V0 V1 (W64 0) (W64 0) sub' = EpochM.bare sub' := by
  unfold resetEpoch; simp

/-- `ChangeReplicationSet`'s new half when it swaps the excluded voter for `x` (an inactive
member of the replication set, or the witness): the old one's regular voters but `x`, and the
old excluded voter back unless it is `x` or the witness. -/
def rsChanged (m : RSM) (x : w64) : RSM :=
  ⟨m.wit, x, (m.nwv \ {[x]}) ∪ (if m.excl ≠ x ∧ m.excl ≠ m.wit then {[m.excl]} else ∅)⟩

/-- A half with an excluded voter has a witness. -/
theorem RSWF.wit_nz {V : GSet w64} {w : w64} {m : RSM} (H : RSWF V w m) (Hx : m.excl ≠ W64 0) :
    m.wit ≠ W64 0 := by
  rcases H.2.1 with h | h
  · rw [← h]; exact Hx
  · exact h.2.2

/-- ... which is a voter of the half, as is its excluded voter. -/
theorem RSWF.mem {V : GSet w64} {w : w64} {m : RSM} (H : RSWF V w m) (Hx : m.excl ≠ W64 0) :
    m.wit ∈ V ∧ m.excl ∈ V := by
  have Hw := H.wit_nz Hx
  have HwV : m.wit ∈ V := by
    have h1 := H.1
    by_cases hw : w ∈ V
    · rw [if_pos hw] at h1; rw [h1]; exact hw
    · rw [if_neg hw] at h1; exact absurd h1 Hw
  refine ⟨HwV, ?_⟩
  rcases H.2.1 with h | h
  · rw [h]; exact HwV
  · exact h.1

theorem rsChanged_wf {V : GSet w64} {w : w64} {m : RSM} (x : w64) (H : RSWF V w m)
    (Hw : m.wit ≠ W64 0) (Hx : x = m.wit ∨ x ∈ m.nwv) : RSWF V w (rsChanged m x) := by
  obtain ⟨H1, H2, H3⟩ := H
  refine ⟨H1, ?_, ?_⟩
  · simp only [rsChanged]
    rcases Hx with h | h
    · exact Or.inl h
    · rw [H3, elem_of_difference, elem_of_union, elem_of_singleton, elem_of_singleton] at h
      exact Or.inr ⟨h.1, fun e => h.2 (Or.inl e), Hw⟩
  · simp only [rsChanged]
    apply set_eq; intro k
    rw [H3]
    simp only [elem_of_union, elem_of_difference, elem_of_singleton]
    by_cases hc : m.excl ≠ x ∧ m.excl ≠ m.wit
    · rw [if_pos hc, elem_of_singleton]
      constructor
      · rintro (⟨⟨hk, hn⟩, hx⟩ | rfl)
        · exact ⟨hk, fun e => e.elim (fun e => hn (Or.inl e)) hx⟩
        · refine ⟨?_, fun e => e.elim hc.2 hc.1⟩
          rcases H2 with h | h
          · exact absurd h hc.2
          · exact h.1
      · rintro ⟨hk, hn⟩
        by_cases he : k = m.excl
        · exact Or.inr he
        · exact Or.inl ⟨⟨hk, fun e => e.elim (fun e => hn (Or.inl e)) he⟩,
            fun e => hn (Or.inr e)⟩
    · rw [if_neg hc]
      constructor
      · rintro (⟨⟨hk, hn⟩, hx⟩ | h)
        · exact ⟨hk, fun e => e.elim (fun e => hn (Or.inl e)) hx⟩
        · exact absurd h (not_elem_of_empty k)
      · rintro ⟨hk, hn⟩
        refine Or.inl ⟨⟨hk, fun e => e.elim (fun e => hn (Or.inl e)) (fun e => ?_)⟩,
          fun e => hn (Or.inr e)⟩
        -- `k` is the old excluded voter: it is `x` or the witness
        subst e
        have : m.excl = x ∨ m.excl = m.wit := by
          by_cases h1 : m.excl = x
          · exact Or.inl h1
          · exact Or.inr (Classical.byContradiction fun h2 => hc ⟨h1, h2⟩)
        exact hn (this.elim Or.inr Or.inl)

theorem take_succ_of (keys : List w64) (i : Int) (key : w64) (Hi : 0 ≤ i)
    (Hkey : keys[i.toNat]? = some key) :
    keys.take (i + 1).toNat = keys.take i.toNat ++ [key] := by
  rw [show (i + 1).toNat = i.toNat + 1 by omega]
  rw [List.take_add_one, Hkey]; rfl

/-- The voter loop's result: the witness if the half has it, and the voter map the half's
voters but it. -/
theorem reset_done (V : GSet w64) (w : w64) (keys : List w64) (mv : GMap w64 Unit)
    (Hkset : ∀ k, k ∈ keys ↔ (V !! k).isSome)
    (Hmv : ∀ k, k ∈ domSet mv ↔ k ∈ keys ∧ k ≠ w) :
    domSet mv = V \ {[w]} ∧ (w ∈ keys ↔ w ∈ V) := by
  refine ⟨set_eq fun k => ?_, Hkset w⟩
  rw [Hmv, elem_of_difference, elem_of_singleton, Hkset]
  rfl

/-- One step of the voter loop at a voter `key`. -/
theorem reset_step (keys : List w64) (i : Int) (key w : w64) (mv : GMap w64 Unit)
    (Hi : 0 ≤ i) (Hkey : keys[i.toNat]? = some key)
    (Hmv : ∀ k, k ∈ domSet mv ↔ k ∈ keys.take i.toNat ∧ k ≠ w) :
    (key = w → (∀ k, k ∈ domSet mv ↔ k ∈ keys.take (i + 1).toNat ∧ k ≠ w) ∧
      w ∈ keys.take (i + 1).toNat) ∧
    (key ≠ w → (∀ k, k ∈ domSet (<[key := ()]> mv) ↔ k ∈ keys.take (i + 1).toNat ∧ k ≠ w) ∧
      (w ∈ keys.take (i + 1).toNat ↔ w ∈ keys.take i.toNat)) := by
  rw [take_succ_of keys i key Hi Hkey]
  refine ⟨fun h => ⟨fun k => ?_, ?_⟩, fun h => ⟨fun k => ?_, ?_⟩⟩
  · rw [Hmv, List.mem_append, List.mem_singleton]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨Or.inl h1, h2⟩
    · rintro ⟨h1 | h1, h2⟩
      · exact ⟨h1, h2⟩
      · exact absurd (h1.trans h) h2
  · rw [List.mem_append, List.mem_singleton]; exact Or.inr h.symm
  · rw [GMap.dom_insert, GMap.elem_of_union, GMap.elem_of_singleton, Hmv, List.mem_append,
      List.mem_singleton]
    constructor
    · rintro (h1 | ⟨h1, h2⟩)
      · subst h1; exact ⟨Or.inr rfl, h⟩
      · exact ⟨Or.inl h1, h2⟩
    · rintro ⟨h1 | h1, h2⟩
      · exact Or.inr ⟨h1, h2⟩
      · exact Or.inl h1
  · rw [List.mem_append, List.mem_singleton]
    constructor
    · rintro (h1 | h1)
      · exact h1
      · exact absurd h1.symm h
    · exact Or.inl

/-- `ChangeReplicationSet`'s rebuilt voter map: the old one's ids but `x` (`mv`), and the old
excluded voter back unless it is `x` or the witness. -/
theorem chg_dom (m : RSM) (x : w64) (ids mv : GMap w64 Unit) (Hmv : domSet mv = ids \ {[x]})
    (Hd : domSet ids = m.nwv) :
    domSet (if m.excl ≠ x ∧ m.excl ≠ m.wit then <[m.excl := ()]> mv else mv) =
      (rsChanged m x).nwv := by
  have hm : ∀ k, k ∈ domSet mv ↔ k ∈ m.nwv ∧ k ≠ x := by
    intro k; rw [Hmv, elem_of_difference, elem_of_singleton, ← Hd, elem_of_dom']
  simp only [rsChanged]
  apply set_eq; intro k
  by_cases hc : m.excl ≠ x ∧ m.excl ≠ m.wit
  · rw [if_pos hc, if_pos hc, dom_insert, elem_of_union, elem_of_singleton, hm, elem_of_union,
      elem_of_difference, elem_of_singleton, elem_of_singleton]
    exact Or.comm
  · rw [if_neg hc, if_neg hc, hm, elem_of_union, elem_of_difference, elem_of_singleton]
    constructor
    · intro h; exact Or.inl h
    · rintro (h | h)
      · exact h
      · exact absurd h (not_elem_of_empty k)

section own
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- A read-only id set (a `map[uint64]struct{}`) holding `S`, or nil for none: an installed
epoch's `NonWitnessVoters`, a `scopedAckIndexer`'s scope. -/
def ownScope (m : Loc) (S : GSet w64) : IProp GF :=
  iprop(⌜m = map.nil ∧ S = ∅⌝ ∨ ∃ ids : GMap w64 Unit, ⌜domSet ids = S⌝ ∗ m ↦$□ ids)

instance ownScope_persistent (m : Loc) (S : GSet w64) : Persistent (ownScope (GF := GF) m S) := by
  unfold ownScope; infer_instance

/-- One half's `ReplicationSet` value holding `m`: its witness and excluded voter, and its
non-witness voters a read-only map (nobody writes an epoch's maps once it is installed), or nil
for none. -/
def ownRS (r : tracker.ReplicationSet) (m : RSM) : IProp GF :=
  iprop(⌜r.Witness' = m.wit ∧ r.Excluded' = m.excl⌝ ∗ ownScope r.NonWitnessVoters' m.nwv)

instance ownRS_persistent (r : tracker.ReplicationSet) (m : RSM) :
    Persistent (ownRS (GF := GF) r m) := by
  unfold ownRS; infer_instance

/-- The tracker's epoch at `e` holds `em`: an `Epoch` nobody writes in place
(`ResetReplicationSet` and `ChangeReplicationSet` allocate a new one), hence persistent. -/
def ownEpoch (e : Loc) (em : EpochM) : IProp GF :=
  iprop(∃ (ev : tracker.Epoch) (r0 r1 : tracker.ReplicationSet), e ↦□ ev ∗
    ⌜ev.Subterm' = em.sub ∧ ev.ReplicationSet'.arr = [r0, r1]⌝ ∗
    ownRS r0 em.rs0 ∗ ownRS r1 em.rs1)

instance ownEpoch_persistent (e : Loc) (em : EpochM) : Persistent (ownEpoch (GF := GF) e em) := by
  unfold ownEpoch; infer_instance

/-- A zero half is the bare one. -/
theorem ownRS_zero : ⊢ ownRS (GF := GF) (zero_val tracker.ReplicationSet) RSM.bare := by
  unfold ownRS ownScope
  isplitr
  · ipureintro; exact ⟨rfl, rfl⟩
  · ileft; ipureintro; exact ⟨rfl, rfl⟩

/-- An epoch with zero halves (`MakeProgressTracker`'s, `ResetReplicationSet`'s early return) is
the bare one at its subterm. -/
theorem ownEpoch_bare_intro (e : Loc) (ev : tracker.Epoch) (s : w64)
    (Hs : ev.Subterm' = s)
    (Ha : ev.ReplicationSet'.arr = [zero_val tracker.ReplicationSet, zero_val tracker.ReplicationSet]) :
    (e ↦□ ev : IProp GF) ⊢ ownEpoch e (EpochM.bare s) := by
  iintro #He
  unfold ownEpoch
  iexists ev, zero_val tracker.ReplicationSet, zero_val tracker.ReplicationSet
  iframe He
  isplitr
  · ipureintro; exact ⟨Hs, Ha⟩
  simp only [EpochM.bare]
  isplitr <;> iapply ownRS_zero

/-- `array_acc`, putting back the same element. (Moved here from `InvTracker.lean`, which
imports this file.) -/
theorem array_acc_same {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (p : Loc)
    (i : Int) (dq : DFrac) (n : Int) (a : GoArray V n) (v : V)
    (hpos : 0 ≤ i) (hlookup : a.arr[i.toNat]? = some v) :
    typedPointsto (GF := GF) p a dq ⊢
      iprop(typedPointsto (arrayIndexRef V i p) v dq ∗
        (typedPointsto (arrayIndexRef V i p) v dq -∗ typedPointsto p a dq)) := by
  have hset : a.arr.set i.toNat v = a.arr := by
    obtain ⟨h, rfl⟩ := List.getElem?_eq_some_iff.1 hlookup
    exact List.set_getElem_self h
  iintro Ha
  icases array_acc (GF := GF) p i dq n a v hpos hlookup $$ Ha with ⟨Hv, Ha⟩
  iframe Hv
  iintro Hv
  ihave Ha := Ha $$ %v Hv
  rw [hset]
  iexact Ha

/-- A half's fields the tracker's functions read, each persistent. -/
theorem ownRS_fields (l : Loc) (r : tracker.ReplicationSet) (m : RSM) :
    (l ↦□ r ∗ ownRS r m : IProp GF) ⊢
      l.[tracker.ReplicationSet, go!"Witness"] ↦□ m.wit ∗
      l.[tracker.ReplicationSet, go!"Excluded"] ↦□ m.excl ∗
      l.[tracker.ReplicationSet, go!"NonWitnessVoters"] ↦□ r.NonWitnessVoters' := by
  iintro ⟨#Hr, #Hm⟩
  iunfold ownRS at Hm
  icases Hm with ⟨%Hwe, -⟩
  obtain ⟨Hw, He⟩ := Hwe
  icases (Access.access (A := iprop(l.[tracker.ReplicationSet, go!"Witness"] ↦□ r.Witness'))
    (A' := iprop(l.[tracker.ReplicationSet, go!"Witness"] ↦□ r.Witness'))
    (P := iprop(l ↦□ r))) $$ Hr with ⟨#Hw', -⟩
  icases (Access.access (A := iprop(l.[tracker.ReplicationSet, go!"Excluded"] ↦□ r.Excluded'))
    (A' := iprop(l.[tracker.ReplicationSet, go!"Excluded"] ↦□ r.Excluded'))
    (P := iprop(l ↦□ r))) $$ Hr with ⟨#He', -⟩
  icases (Access.access
    (A := iprop(l.[tracker.ReplicationSet, go!"NonWitnessVoters"] ↦□ r.NonWitnessVoters'))
    (A' := iprop(l.[tracker.ReplicationSet, go!"NonWitnessVoters"] ↦□ r.NonWitnessVoters'))
    (P := iprop(l ↦□ r))) $$ Hr with ⟨#Hn', -⟩
  rw [← Hw, ← He]
  iframe Hw' He' Hn'

/-- The epoch's fields: the subterm, and each half's replication set (its value, and what it
holds). -/
theorem ownEpoch_fields (e : Loc) (em : EpochM) :
    ownEpoch (GF := GF) e em ⊢
      e.[tracker.Epoch, go!"Subterm"] ↦□ em.sub ∗
      (∃ r0 : tracker.ReplicationSet, arrayIndexRef tracker.ReplicationSet (sint.Z (W64 0)) e.[tracker.Epoch, go!"ReplicationSet"] ↦□ r0 ∗ ownRS r0 em.rs0) ∗
      (∃ r1 : tracker.ReplicationSet, arrayIndexRef tracker.ReplicationSet (sint.Z (W64 1)) e.[tracker.Epoch, go!"ReplicationSet"] ↦□ r1 ∗ ownRS r1 em.rs1) := by
  iintro He
  iunfold ownEpoch at He
  icases He with ⟨%ev, %r0, %r1, #Hev, %Hsa, #H0, #H1⟩
  obtain ⟨Hsub, Harr⟩ := Hsa
  icases (Access.access (A := iprop(e.[tracker.Epoch, go!"Subterm"] ↦□ ev.Subterm'))
    (A' := iprop(e.[tracker.Epoch, go!"Subterm"] ↦□ ev.Subterm'))
    (P := iprop(e ↦□ ev))) $$ Hev with ⟨#Hs, -⟩
  icases (Access.access (A := iprop(e.[tracker.Epoch, go!"ReplicationSet"] ↦□ ev.ReplicationSet'))
    (A' := iprop(e.[tracker.Epoch, go!"ReplicationSet"] ↦□ ev.ReplicationSet'))
    (P := iprop(e ↦□ ev))) $$ Hev with ⟨#Hrs, -⟩
  icases array_acc_same _ (sint.Z (W64 0)) _ _ _ r0 (by decide) (by rw [Harr]; rfl) $$ Hrs
    with ⟨#Hr0, -⟩
  icases array_acc_same _ (sint.Z (W64 1)) _ _ _ r1 (by decide) (by rw [Harr]; rfl) $$ Hrs
    with ⟨#Hr1, -⟩
  rw [← Hsub]
  iframe Hs
  isplitl
  · iexists r0; iframe Hr0 H0
  · iexists r1; iframe Hr1 H1

/-- An epoch's two fields, out of its struct. -/
theorem epoch_split (l : Loc) (ev : tracker.Epoch) :
    (l ↦ ev : IProp GF) ⊢ ⌜l ≠ null⌝ ∗ l.[tracker.Epoch, go!"Subterm"] ↦ ev.Subterm' ∗
      l.[tracker.Epoch, go!"ReplicationSet"] ↦ ev.ReplicationSet' := by
  iintro H
  icases typedPointsto_not_null_dup _ _ _ $$ H with ⟨H, %Hnn⟩
  icases typedPointsto_split _ _ _ $$ H with H
  simp only [TypedPointsto.typedPointstoDef]
  icases H with ⟨H1, H2, -⟩
  iframe H1 H2
  ipureintro; exact Hnn

/-- ... and back. -/
theorem epoch_combine (l : Loc) (s : w64) (a : GoArray tracker.ReplicationSet 2) (Hnn : l ≠ null) :
    (l.[tracker.Epoch, go!"Subterm"] ↦ s ∗ l.[tracker.Epoch, go!"ReplicationSet"] ↦ a : IProp GF) ⊢
      l ↦ tracker.Epoch.mk s a := by
  iintro ⟨H1, H2⟩
  iapply typedPointsto_combine _ _ _ Hnn
  simp only [TypedPointsto.typedPointstoDef]
  iframe H1 H2

/-- A half `ResetReplicationSet` has built, its voter map still owned. -/
def ownRSb (r : tracker.ReplicationSet) (m : RSM) : IProp GF :=
  iprop(⌜r.Witness' = m.wit ∧ r.Excluded' = m.excl⌝ ∗
    ∃ ids : GMap w64 Unit, ⌜domSet ids = m.nwv⌝ ∗ r.NonWitnessVoters' ↦$ ids)

theorem ownRSb_persist (r : tracker.ReplicationSet) (m : RSM) :
    ownRSb (GF := GF) r m ⊢ |==> ownRS r m := by
  unfold ownRSb
  iintro ⟨%Hwe, %ids, %Hd, Hm⟩
  imod ownMap_persist _ _ _ $$ Hm with #Hm
  imodintro
  unfold ownRS ownScope
  isplitr
  · ipureintro; exact Hwe
  iright
  iexists ids
  iframe Hm
  ipureintro; exact Hd

/-- A half's witness and excluded voter, persistent. -/
theorem ownEpoch_we (e : Loc) (em : EpochM) :
    ownEpoch (GF := GF) e em ⊢
      (arrayIndexRef tracker.ReplicationSet (sint.Z (W64 0)) e.[tracker.Epoch, go!"ReplicationSet"]).[tracker.ReplicationSet, go!"Witness"] ↦□ em.rs0.wit ∗
      (arrayIndexRef tracker.ReplicationSet (sint.Z (W64 0)) e.[tracker.Epoch, go!"ReplicationSet"]).[tracker.ReplicationSet, go!"Excluded"] ↦□ em.rs0.excl ∗
      (arrayIndexRef tracker.ReplicationSet (sint.Z (W64 1)) e.[tracker.Epoch, go!"ReplicationSet"]).[tracker.ReplicationSet, go!"Witness"] ↦□ em.rs1.wit ∗
      (arrayIndexRef tracker.ReplicationSet (sint.Z (W64 1)) e.[tracker.Epoch, go!"ReplicationSet"]).[tracker.ReplicationSet, go!"Excluded"] ↦□ em.rs1.excl := by
  iintro #He
  icases ownEpoch_fields e em $$ He with ⟨-, ⟨%r0, #Hr0, #H0⟩, ⟨%r1, #Hr1, #H1⟩⟩
  icases ownRS_fields _ r0 em.rs0 $$ [Hr0 H0] with ⟨#Hw0, #He0, -⟩
  · iframe Hr0 H0
  icases ownRS_fields _ r1 em.rs1 $$ [Hr1 H1] with ⟨#Hw1, #He1, -⟩
  · iframe Hr1 H1
  iframe Hw0 He0 Hw1 He1

end own

end EtcdGrove
end Perennial
