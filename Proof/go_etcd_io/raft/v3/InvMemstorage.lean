/-
`MemoryStorage`'s representation predicates over the range vocabulary (U8 v2 step 3, 2026-10-29;
candidate 17 rev 3 §6, `notes/spec-first-study/raft-storage-spec.md`; `notes/raft-unified-plan.md`,
"U8 v2"). Until U8 v2 this file held the old contract's machinery (the owner's history `hist`, the
writer's `done`, the hand-out `ep`, the floor and the certificate registry); all of it is gone.

### Ghost state (`MemStorNames`)

- `log`: a ghost map `index ↦ entry`; its fragments are the ranges (`memLog γs k dq es`, the
  instance's `storLog`, fractional, a discarded fragment frozen). The lock holds its authority.
  Keys below the compaction point keep the entries they had ("or compacted"); keys at or past the
  end are absent (so `Append` can add them); the entry at the compaction point is frozen in the lock
  (the dummy, of the term `Term(c)` answers: nobody can rewrite it).
- `en`, `ek`: the end (`memEnd γs e`, the instance's `storEnd`): half of a ghost variable (the
  other half the lock's) and an exclusive token (so that two ends contradict).
- `cp`: the compaction point, a monotone counter (the lock's authority); `jc`: the compaction
  points justified so far, a monotone list (`memCompacted γs c`, the instance's `storCompacted`,
  is a lower bound of both). Its authority is in the justification invariant (`memJustInv`), with
  the justification `J.B k` of every element: `storCompacted_bound` opens it (`memCompacted_bound`).
- `sx`: the stored snapshot, a ghost variable split in three: the client's half (`memSnapExact γs
  sv`, the kvreconf single writer's), a quarter the lock's, a quarter the snapshot's home's.
- `lk`: the lock's key, which takes the snapshot out of its home (`memSnapHome`, in the
  justification invariant: the snapshot, physically, and its validity `J.SV sv ∗ J.DL i`) for a
  critical section.

### The justification parameters (`MemJust`)

The compaction point's justification (`J.B`: the API's `nodeAppliedLb γ id k ∨ snapGiven γ id k`),
the stored snapshot's validity (`J.SV`: `snapshotValid γ`) and its delivered bound (`J.DL`: the
API's `deliveredLogLb` of the node, or `snapGiven`) are cluster-level, so this file states them as
parameters, as `isStorageP SV Bnd DL` does: **step 4 instantiates `J`** to the API's names and
`memStorInvP ms γs J` to the approved `memStorInv ms γs γ id`. `J.B` is timeless (`storCompacted_bound`
reads it under an update with no program step).

### Lifecycle

`NewMemoryStorage` gives the lock (`memStorLock`), the frozen dummy at `0`, the end at `1`, the
client's snapshot half at the empty snapshot, the hard state (`memStorMeta`) and the allocation's
fuel (`memStorFresh`: the authority of `jc` and the snapshot's home, which the lock does not hold
until then). `InitialState` reads the snapshot without the lock, so it is specified on
`memStorFresh` (before the justification invariant exists). `memStorInvP_alloc` turns the fuel
into the invariant (`memStorInvP ms γs J`, persistent), from which the methods that need the
justifications (`Snapshot`, `ApplySnapshot`, `CreateSnapshot`, `Compact`) and the contract law
(`MemstorageInstance.lean`) follow.
-/
module

public import Proof.go_etcd_io.raft.v3.InvStorage
public import Proof.go_etcd_io.raft.v3.Protocol.Ghost

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-- The storage's physical state as the private helpers (`lastIndex`, `firstIndex`) see it: the
dummy's id `p` (index and term of the compaction point) and the entries after it. -/
def memPhys (p : entryID) (ents : List EntryM) : StorState :=
  { prev := p, ents := ents, pend := [] }

/-- The empty snapshot, `NewMemoryStorage`'s (`EnsureSnapshot(nil)`). -/
def memSnapEmpty : SnapshotM :=
  SnapshotM.mk [] (SnapshotMetadataM.mk (ConfStateM.mk [] [] [] [] false) (W64 0) (W64 0))

/-- The dummy entry `ApplySnapshot(sv)` stores (`{Term: sv.Term, Index: sv.Index}`). -/
def memDummy (sv : SnapshotM) : EntryM :=
  EntryM.mk sv.Metadata'.Term' sv.Metadata'.Index' zeroValDef []

/-- The snapshot `CreateSnapshot(i, cs, data)` leaves from the stored `sv0`: index `i`, term `t`,
the conf state `*cs` when given (`oc`), else the stored one's, the data `bs`. -/
def memSnapCreated (sv0 : SnapshotM) (i t : w64) (oc : Option ConfStateM) (bs : List w8) :
    SnapshotM :=
  SnapshotM.mk bs (SnapshotMetadataM.mk (oc.getD sv0.Metadata'.ConfState') i t)

/-- What the lock knows of its state: the compaction point `c` (the dummy's index), the entries
`ents` after it, the ghost map `M` and the stored snapshot `sv`. The end `c + 1 + |ents|` is at
most `2^61`; the map has the physical entries strictly between the compaction point and the end,
and nothing at or past the end; the stored snapshot's index is at or past the compaction point and
below the end. -/
def MemOk (p : entryID) (ents : List EntryM) (M : GMap Nat EntryM) (sv : SnapshotM) : Prop :=
  uint.nat p.index' + 1 + ents.length ≤ 2^61 ∧
  (∀ i, uint.nat p.index' + 1 + ents.length ≤ i → M.lookup i = none) ∧
  (∀ i, uint.nat p.index' < i → i < uint.nat p.index' + 1 + ents.length →
    M.lookup i = ents[i - uint.nat p.index' - 1]?) ∧
  uint.nat p.index' ≤ uint.nat sv.Metadata'.Index' ∧
  uint.nat sv.Metadata'.Index' < uint.nat p.index' + 1 + ents.length

end pure

/-- The ghost names of a `MemoryStorage` (U8 v2 step 3): see the file header. -/
structure MemStorNames where
  log : GName
  en : GName
  ek : GName
  cp : GName
  jc : GName
  sx : GName
  lk : GName
  /-- the snapshot's home's key (two homes contradict) -/
  hk : GName

/-- **The justification parameters** (see the file header): step 4 instantiates them to the API's
names. -/
structure MemJust (GF : BundledGFunctors) where
  /-- a non-empty stored snapshot's validity (the API's `snapshotValid γ`) -/
  SV : SnapshotM → IProp GF
  /-- why the storage may be compacted to `k` (the API's `nodeAppliedLb γ id k ∨ snapGiven γ id k`) -/
  B : Nat → IProp GF
  /-- why a stored snapshot at `i` is at most what raft has committed (the API's delivered prefix) -/
  DL : Nat → IProp GF
  SV_pers : ∀ sv, Persistent (SV sv)
  B_pers : ∀ k, Persistent (B k)
  B_timeless : ∀ k, Timeless (B k)
  DL_pers : ∀ i, Persistent (DL i)

instance MemJust.SV_persistent {GF : BundledGFunctors} (J : MemJust GF) (sv : SnapshotM) :
    Persistent (J.SV sv) := J.SV_pers sv
instance MemJust.B_persistent {GF : BundledGFunctors} (J : MemJust GF) (k : Nat) :
    Persistent (J.B k) := J.B_pers k
instance MemJust.B_timeless' {GF : BundledGFunctors} (J : MemJust GF) (k : Nat) :
    Timeless (J.B k) := J.B_timeless k
instance MemJust.DL_persistent {GF : BundledGFunctors} (J : MemJust GF) (i : Nat) :
    Persistent (J.DL i) := J.DL_pers i

/-- The contract's compaction justification for `J` (`isStorageP`'s `Bnd`): some justified point
at or past `c`. -/
def memBnd {GF : BundledGFunctors} (J : MemJust GF) (c : Nat) : IProp GF :=
  iprop(∃ (k : Nat), ⌜c ≤ k⌝ ∗ J.B k)

instance memBnd_pers {GF : BundledGFunctors} (J : MemJust GF) (c : Nat) :
    Persistent (memBnd J c) := by
  unfold memBnd; infer_instance

section ghost
variable [GooseExts] {GF : BundledGFunctors} [AllG GF]

/-- A key: an exclusive token. -/
def memKey (γ : GName) : IProp GF := ghostVar γ 1 ()

instance memKey_timeless (γ : GName) : Timeless (memKey (GF := GF) γ) := by
  unfold memKey; infer_instance

theorem memKey_excl (γ : GName) : ⊢ memKey (GF := GF) γ -∗ memKey γ -∗ False := by
  iintro H1 H2
  iunfold memKey at H1 H2
  icases ghostVar_valid_2 γ () 1 () 1 $$ H1 H2 with %H
  exfalso
  obtain ⟨H, -⟩ := H
  grind

/-- A quarter. -/
abbrev memQ : Qp := (1 : Qp).half.half

/-! ### Ranges of the log -/

/-- The entries `es` at the indices `k, k+1, …` of the ghost map `γ`, at `dq`. -/
def memLogL (γ : GName) (k : Nat) (dq : DFrac) : List EntryM → IProp GF
  | [] => iprop(emp)
  | e :: es => iprop(k ↪[γ]{dq} e ∗ memLogL γ (k + 1) dq es)

instance memLogL_timeless (γ : GName) (k : Nat) (dq : DFrac) (es : List EntryM) :
    Timeless (memLogL (GF := GF) γ k dq es) := by
  induction es generalizing k with
  | nil => unfold memLogL; infer_instance
  | cons e es ih => unfold memLogL; infer_instance

instance memLogL_persistent (γ : GName) (k : Nat) (es : List EntryM) :
    Persistent (memLogL (GF := GF) γ k DFrac.discard es) := by
  induction es generalizing k with
  | nil => unfold memLogL; infer_instance
  | cons e es ih => unfold memLogL; infer_instance

theorem memLogL_app (γ : GName) (k : Nat) (dq : DFrac) (a b : List EntryM) :
    memLogL (GF := GF) γ k dq (a ++ b) ⊣⊢ memLogL γ k dq a ∗ memLogL γ (k + a.length) dq b := by
  induction a generalizing k with
  | nil =>
    simp only [List.nil_append, List.length_nil, Nat.add_zero, memLogL]
    exact emp_sep.symm
  | cons e a ih =>
    simp only [List.cons_append, memLogL, List.length_cons]
    rw [show k + (a.length + 1) = (k + 1) + a.length by omega]
    exact (sep_congr .rfl (ih (k + 1))).trans sep_assoc.symm

/-- A fragment's fraction splits. -/
theorem memElem_frac (γ : GName) (k : Nat) (dq1 dq2 : DFrac) (e : EntryM) :
    (k ↪[γ]{dq1 • dq2} e : IProp GF) ⊣⊢ k ↪[γ]{dq1} e ∗ k ↪[γ]{dq2} e := by
  constructor
  · unfold ghostMapElem
    have h : (HeapView.Frag (H := GMap Pos) (Pos.Countable.encode k) (dq1 • dq2) (encV e)) =
        (HeapView.Frag (H := GMap Pos) (Pos.Countable.encode k) dq1 (encV e) •
          HeapView.Frag (H := GMap Pos) (Pos.Countable.encode k) dq2 (encV e) : HeapView _ _ _) := by
      rw [← HeapView.frag_op_eqv, Agree.idemp]
    rw [h]
    exact (own_op _ _ _).1
  · iintro ⟨H1, H2⟩
    icases ghostMapElem_combine k γ dq1 dq2 e e $$ H1 H2 with ⟨H, -⟩
    iexact H

theorem memLogL_frac (γ : GName) (k : Nat) (dq1 dq2 : DFrac) (es : List EntryM) :
    memLogL (GF := GF) γ k (dq1 • dq2) es ⊣⊢ memLogL γ k dq1 es ∗ memLogL γ k dq2 es := by
  induction es generalizing k with
  | nil => simp only [memLogL]; exact (sep_emp (PROP := IProp GF)).symm
  | cons e es ih =>
    simp only [memLogL]
    refine (sep_congr (memElem_frac γ k dq1 dq2 e) (ih (k + 1))).trans ?_
    · constructor
      · iintro ⟨⟨H1, H2⟩, H3, H4⟩; iframe
      · iintro ⟨⟨H1, H3⟩, H2, H4⟩; iframe

theorem memLogL_persist (γ : GName) (k : Nat) (dq : DFrac) (es : List EntryM) :
    ⊢ memLogL (GF := GF) γ k dq es ==∗ memLogL γ k DFrac.discard es := by
  induction es generalizing k with
  | nil => iintro -; imodintro; simp only [memLogL]; iempintro
  | cons e es ih =>
    iintro H
    simp only [memLogL]
    icases H with ⟨H1, H2⟩
    imod ghostMapElem_persist k γ dq e $$ H1 with H1
    imod ih (k + 1) $$ H2 with H2
    imodintro
    iframe

/-- An element of a range. -/
theorem memLogL_lookup (γ : GName) (k : Nat) (dq : DFrac) (es : List EntryM) (j : Nat)
    (e : EntryM) (h : es[j]? = some e) :
    memLogL (GF := GF) γ k dq es ⊢ (k + j) ↪[γ]{dq} e ∗ ((k + j) ↪[γ]{dq} e -∗ memLogL γ k dq es) := by
  induction es generalizing k j with
  | nil => simp at h
  | cons e0 es ih =>
    simp only [memLogL]
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      iintro ⟨H1, H2⟩
      iframe H1
      iintro H1
      iframe
    | succ j =>
      simp only [List.getElem?_cons_succ] at h
      rw [show k + (j + 1) = (k + 1) + j by omega]
      iintro ⟨H1, H2⟩
      icases ih (k + 1) j h $$ H2 with ⟨H, Hb⟩
      iframe H
      iintro H
      iframe H1
      iapply Hb $$ H

/-- A range's entries are the map's. -/
theorem memLogL_auth (γ : GName) (q : Qp) (M : GMap Nat EntryM) (k : Nat) (dq : DFrac)
    (es : List EntryM) :
    ⊢ ghostMapAuth (GF := GF) γ q M -∗ memLogL γ k dq es -∗
      ⌜∀ j e, es[j]? = some e → M.lookup (k + j) = some e⌝ := by
  induction es generalizing k with
  | nil => iintro - -; ipureintro; intro j e h; simp at h
  | cons e0 es ih =>
    iintro Ha H
    simp only [memLogL]
    icases H with ⟨H1, H2⟩
    icases ghost_map_lookup $$ Ha H1 with %H0
    icases ih (k + 1) $$ Ha H2 with %Hr
    ipureintro
    intro j e h
    cases j with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at h; subst h; simpa using H0
    | succ j =>
      simp only [List.getElem?_cons_succ] at h
      have := Hr j e h
      rwa [show k + 1 + j = k + (j + 1) by omega] at this

/-- An owned range and a frozen element are disjoint. -/
theorem memLogL_frozen_ne (γ : GName) (k : Nat) (es : List EntryM) (i : Nat) (e : EntryM) :
    ⊢ memLogL (GF := GF) γ k (DFrac.own 1) es -∗ i ↪[γ]□ e -∗ ⌜i < k ∨ k + es.length ≤ i⌝ := by
  iintro H #He
  by_cases h : k ≤ i ∧ i < k + es.length
  · obtain ⟨e', he'⟩ : ∃ e', es[i - k]? = some e' :=
      ⟨es[i - k]'(by omega), List.getElem?_eq_getElem (by omega)⟩
    icases memLogL_lookup γ k (DFrac.own 1) es (i - k) e' he' $$ H with ⟨H1, -⟩
    rw [show k + (i - k) = i by omega]
    icases ghostMapElem_ne γ i i DFrac.discard e' e $$ H1 He with %Hne
    exact absurd rfl Hne
  · ipureintro; omega

/-- Delete an owned range from the map. -/
theorem memLogL_delete (γ : GName) (M : GMap Nat EntryM) (k : Nat) (es : List EntryM) :
    ⊢ ghostMapAuth (GF := GF) γ 1 M -∗ memLogL γ k (DFrac.own 1) es ==∗
      ∃ M', ghostMapAuth γ 1 M' ∗
        ⌜∀ i, M'.lookup i = if k ≤ i ∧ i < k + es.length then none else M.lookup i⌝ := by
  induction es generalizing k M with
  | nil =>
    iintro Ha -
    imodintro
    iexists M
    iframe Ha
    ipureintro; intro i; simp only [List.length_nil, Nat.add_zero]; rw [if_neg (by omega)]
  | cons e es ih =>
    iintro Ha H
    simp only [memLogL]
    icases H with ⟨H1, H2⟩
    imod ghost_map_delete $$ Ha H1 with Ha
    imod ih (k := k + 1) (M := M.delete k) $$ Ha H2 with ⟨%M', Ha, %HM'⟩
    imodintro
    iexists M'
    iframe Ha
    ipureintro
    intro i
    rw [HM' i]
    simp only [List.length_cons]
    by_cases hik : i = k
    · subst hik; simp [GMap.lookup_delete_iff]
    · rw [GMap.lookup_delete_ne _ (Ne.symm hik)]
      by_cases h1 : k + 1 ≤ i ∧ i < k + 1 + es.length
      · rw [if_pos h1, if_pos (by omega)]
      · rw [if_neg h1, if_neg (by omega)]

/-- Insert a range of absent keys into the map. -/
theorem memLogL_insert (γ : GName) (M : GMap Nat EntryM) (k : Nat) (es : List EntryM)
    (Habs : ∀ i, k ≤ i → i < k + es.length → M.lookup i = none) :
    ⊢ ghostMapAuth (GF := GF) γ 1 M ==∗
      ∃ M', ghostMapAuth γ 1 M' ∗ memLogL γ k (DFrac.own 1) es ∗
        ⌜∀ i, M'.lookup i = if k ≤ i ∧ i < k + es.length then es[i - k]? else M.lookup i⌝ := by
  induction es generalizing k M with
  | nil =>
    iintro Ha
    imodintro
    iexists M
    iframe Ha
    isplitl []
    · simp only [memLogL]; iempintro
    ipureintro; intro i; simp only [List.length_nil, Nat.add_zero]; rw [if_neg (by omega)]
  | cons e es ih =>
    iintro Ha
    have Hk : M.lookup k = none := Habs k (Nat.le_refl _) (by simp)
    imod ghost_map_insert k e Hk $$ Ha with ⟨Ha, H1⟩
    have Habs' : ∀ i, k + 1 ≤ i → i < k + 1 + es.length → (M.insert k e).lookup i = none := by
      intro i h1 h2
      rw [GMap.lookup_insert_ne _ _ (by omega)]
      exact Habs i (by omega) (by simp; omega)
    imod ih (k := k + 1) (M := M.insert k e) Habs' $$ Ha with ⟨%M', Ha, H2, %HM'⟩
    imodintro
    iexists M'
    iframe Ha
    isplitl [H1 H2]
    · simp only [memLogL]; iframe
    ipureintro
    intro i
    rw [HM' i]
    simp only [List.length_cons]
    by_cases hik : i = k
    · subst hik
      rw [if_neg (by omega), if_pos (by omega), GMap.lookup_insert_eq]
      simp
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm hik)]
      by_cases h1 : k + 1 ≤ i ∧ i < k + 1 + es.length
      · rw [if_pos h1, if_pos (by omega)]
        rw [show i - k = (i - (k + 1)) + 1 by omega, List.getElem?_cons_succ]
      · rw [if_neg h1, if_neg (by omega)]

end ghost

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-! ### The vocabulary at the storage's names -/

/-- **A range** (the instance's `storLog`): the entries `es` from index `k`, at `dq`, and their
last index below `2^61` (the contract's `Hlen`: `Append`'s premise). -/
def memLog (γs : MemStorNames) (k : Nat) (dq : DFrac) (es : List EntryM) : IProp GF :=
  iprop(memLogL γs.log k dq es ∗ ⌜es = [] ∨ k + es.length ≤ 2^61⌝)

instance memLog_persistent (γs : MemStorNames) (k : Nat) (es : List EntryM) :
    Persistent (memLog (GF := GF) γs k DFrac.discard es) := by
  unfold memLog; infer_instance

/-- **The end** (the instance's `storEnd`): the last index is exactly `e - 1`. -/
def memEnd (γs : MemStorNames) (e : Nat) : IProp GF :=
  iprop(ghostVar γs.en (1 : Qp).half e ∗ memKey γs.ek)

/-- **The compaction point has reached `c`** (the instance's `storCompacted`; persistent): `0`,
or a lower bound of the compaction point and of a justified point. -/
def memCompacted (γs : MemStorNames) (c : Nat) : IProp GF :=
  iprop(⌜c = 0⌝ ∨ (monoNatLbOwn γs.cp c ∗
    ∃ (L : List Nat), monoListLbOwn γs.jc L ∗ ⌜∃ k ∈ L, c ≤ k⌝))

instance memCompacted_persistent (γs : MemStorNames) (c : Nat) :
    Persistent (memCompacted (GF := GF) γs c) := by
  unfold memCompacted; infer_instance

/-- **The stored snapshot is exactly `sv`** (G2; the client's, exclusive in practice: kvreconf's
single writer). -/
def memSnapExact (γs : MemStorNames) (sv : SnapshotM) : IProp GF :=
  ghostVar γs.sx (1 : Qp).half sv

theorem memLog_app (γs : MemStorNames) (k : Nat) (dq : DFrac) (a b : List EntryM) :
    memLog (GF := GF) γs k dq (a ++ b) ⊣⊢ memLog γs k dq a ∗ memLog γs (k + a.length) dq b := by
  unfold memLog
  have h1 : (a ++ b = [] ∨ k + (a ++ b).length ≤ 2^61) →
      (a = [] ∨ k + a.length ≤ 2^61) ∧ (b = [] ∨ k + a.length + b.length ≤ 2^61) := by
    intro h
    simp only [List.append_eq_nil_iff, List.length_append] at h
    rcases h with ⟨ha, hb⟩ | h
    · exact ⟨Or.inl ha, Or.inl hb⟩
    · exact ⟨Or.inr (by omega), Or.inr (by omega)⟩
  have h2 : (a = [] ∨ k + a.length ≤ 2^61) → (b = [] ∨ k + a.length + b.length ≤ 2^61) →
      (a ++ b = [] ∨ k + (a ++ b).length ≤ 2^61) := by
    intro ha hb
    simp only [List.append_eq_nil_iff, List.length_append]
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact Or.inl ⟨ha, hb⟩
    · subst ha; right; simp only [List.length_nil] at hb ⊢; omega
    · subst hb; right; simp only [List.length_nil]; omega
    · right; omega
  constructor
  · iintro ⟨H, %Hb⟩
    icases (memLogL_app γs.log k dq a b).1 $$ H with ⟨Ha, Hb'⟩
    obtain ⟨ha, hb⟩ := h1 Hb
    iframe Ha Hb'
    ipureintro; exact ⟨ha, hb⟩
  · iintro ⟨⟨Ha, %Ha⟩, ⟨Hb, %Hb⟩⟩
    isplitl [Ha Hb]
    · iapply (memLogL_app γs.log k dq a b).2; iframe
    ipureintro; exact h2 Ha Hb

theorem memLog_frac (γs : MemStorNames) (k : Nat) (dq1 dq2 : DFrac) (es : List EntryM) :
    memLog (GF := GF) γs k (dq1 • dq2) es ⊣⊢ memLog γs k dq1 es ∗ memLog γs k dq2 es := by
  unfold memLog
  constructor
  · iintro ⟨H, %Hb⟩
    icases (memLogL_frac γs.log k dq1 dq2 es).1 $$ H with ⟨H1, H2⟩
    iframe H1 H2
    ipureintro; exact ⟨Hb, Hb⟩
  · iintro ⟨⟨H1, %Hb⟩, ⟨H2, -⟩⟩
    isplitl [H1 H2]
    · iapply (memLogL_frac γs.log k dq1 dq2 es).2; iframe
    ipureintro; exact Hb

theorem memLog_persist (γs : MemStorNames) (k : Nat) (dq : DFrac) (es : List EntryM) :
    ⊢ memLog (GF := GF) γs k dq es ==∗ memLog γs k DFrac.discard es := by
  unfold memLog
  iintro ⟨H, %Hb⟩
  imod memLogL_persist γs.log k dq es $$ H with H
  imodintro
  iframe H
  ipureintro; exact Hb

theorem memLog_nil (γs : MemStorNames) (k : Nat) (dq : DFrac) :
    ⊢ memLog (GF := GF) γs k dq [] := by
  unfold memLog
  simp only [memLogL]
  iintro
  isplitl []
  · iempintro
  ipureintro; exact Or.inl trivial

theorem memLog_bound (γs : MemStorNames) (k : Nat) (dq : DFrac) (es : List EntryM) :
    memLog (GF := GF) γs k dq es ⊢ ⌜es = [] ∨ k + es.length ≤ 2^61⌝ := by
  unfold memLog
  iintro ⟨-, %H⟩
  ipureintro; exact H

theorem memEnd_excl (γs : MemStorNames) (e e' : Nat) :
    memEnd (GF := GF) γs e ∗ memEnd γs e' ⊢ False := by
  unfold memEnd
  iintro ⟨⟨-, H1⟩, ⟨-, H2⟩⟩
  iapply memKey_excl $$ H1 H2

theorem memCompacted_zero (γs : MemStorNames) : ⊢ memCompacted (GF := GF) γs 0 := by
  unfold memCompacted
  iintro
  ileft; ipureintro; rfl

theorem memCompacted_mono (γs : MemStorNames) (c c' : Nat) (h : c' ≤ c) :
    memCompacted (GF := GF) γs c ⊢ memCompacted γs c' := by
  unfold memCompacted
  iintro (%H | ⟨#H1, %L, #H2, %HL⟩)
  · ileft; ipureintro; omega
  iright
  isplitl []
  · iapply monoNatLbOwn_le c' h $$ H1
  iexists L
  iframe H2
  ipureintro
  obtain ⟨k, hk, hck⟩ := HL
  exact ⟨k, hk, by omega⟩

/-! ### The lock's invariant -/

/-- What the lock protects of the storage's fields: `hardState` (half: the other half is
`memStorMeta`'s), the entries (read-only log entries, the dummy at the compaction point first:
`ents[0]`, made by `NewMemoryStorage`, `ApplySnapshot` or `Compact`) and their capacity, and the
call counters but `initialState` (`memStorMeta`'s). What the private helpers `lastIndex` and
`firstIndex` are specified on (`σ.prev` the dummy's id, `σ.ents` the entries after it). -/
def memstorageFields (ms : Loc) (σ : StorState) : IProp GF :=
  iprop(∃ (hp : Loc) (es : GoSlice) (dummy : EntryM) (nfi nli nen nte nsn : w64),
  "HhardState" ∷ ms.[MemoryStorage, go!"hardState"] ↦{DFrac.own (1 : Qp).half} hp ∗
  "Hents_f" ∷ ms.[MemoryStorage, go!"ents"] ↦ es ∗
  "Hents" ∷ entsRO es (dummy :: σ.ents) ∗
  "Hents_cap" ∷ ownSliceCap Loc es (DFrac.own 1) ∗
  "%Hdummy" ∷ ⌜dummy.Index' = σ.prev.index' ∧ dummy.Term' = σ.prev.term'⌝ ∗
  "Hcs_firstIndex" ∷ (ms.[MemoryStorage, go!"callStats"]).[inMemStorageCallStats, go!"firstIndex"] ↦ nfi ∗
  "Hcs_lastIndex" ∷ (ms.[MemoryStorage, go!"callStats"]).[inMemStorageCallStats, go!"lastIndex"] ↦ nli ∗
  "Hcs_entries" ∷ (ms.[MemoryStorage, go!"callStats"]).[inMemStorageCallStats, go!"entries"] ↦ nen ∗
  "Hcs_term" ∷ (ms.[MemoryStorage, go!"callStats"]).[inMemStorageCallStats, go!"term"] ↦ nte ∗
  "Hcs_snapshot" ∷ (ms.[MemoryStorage, go!"callStats"]).[inMemStorageCallStats, go!"snapshot"] ↦ nsn)

/-- The fields read only the boundary and the entries. -/
theorem memstorageFields_congr (ms : Loc) (σ σ' : StorState) (h1 : σ'.prev = σ.prev)
    (h2 : σ'.ents = σ.ents) :
    memstorageFields (GF := GF) ms σ ⊢ memstorageFields ms σ' := by
  unfold memstorageFields
  rw [h1, h2]

/-- `c` is a justified compaction point (persistent): an element of `jc`. -/
def memCompJust (γs : MemStorNames) (c : Nat) : IProp GF :=
  iprop(∃ (L : List Nat), monoListLbOwn γs.jc L ∗ ⌜c ∈ L⌝)

instance memCompJust_persistent (γs : MemStorNames) (c : Nat) :
    Persistent (memCompJust (GF := GF) γs c) := by
  unfold memCompJust; infer_instance

/-- **The lock's invariant** (γ-free): the fields at the dummy's id `p` (the compaction point
`c = p.index`) and the entries `ents` after it; the log's map `M` (its authority), the end's half,
the compaction point's authority and its justification's registration, the lock's quarter of the
stored snapshot `sv` and the lock's key; the dummy frozen in the map, of the dummy's term (so no
range a client owns covers it, and `Term(c)` answers what any range says), and the stored
snapshot's index frozen likewise, unless it is `0` (so `ApplySnapshot`, given an owned range from
`j ≤ s` to the end, finds it below `s`); and `MemOk`. -/
def memstorageInv (ms : Loc) (γs : MemStorNames) : IProp GF :=
  iprop(∃ (p : entryID) (ents : List EntryM) (M : GMap Nat EntryM) (sv : SnapshotM),
  "Hfields" ∷ memstorageFields ms (memPhys p ents) ∗
  "Hlog" ∷ ghostMapAuth γs.log 1 M ∗
  "Hen" ∷ ghostVar γs.en (1 : Qp).half (uint.nat p.index' + 1 + ents.length) ∗
  "Hcp" ∷ monoNatAuthOwn γs.cp 1 (uint.nat p.index') ∗
  "#Hcj" ∷ memCompJust γs (uint.nat p.index') ∗
  "Hsx" ∷ ghostVar γs.sx memQ sv ∗
  "Hlk" ∷ memKey γs.lk ∗
  "#Hd0" ∷ (∃ (e0 : EntryM), (uint.nat p.index') ↪[γs.log]□ e0 ∗ ⌜e0.Term' = p.term'⌝) ∗
  "#Hsf" ∷ (⌜uint.nat sv.Metadata'.Index' = 0⌝ ∨ ∃ (e : EntryM),
     (uint.nat sv.Metadata'.Index') ↪[γs.log]□ e ∗ ⌜e.Term' = sv.Metadata'.Term'⌝) ∗
  "%Hok" ∷ ⌜MemOk p ents M sv⌝)

/-- The storage's lock (persistent; `NewMemoryStorage`'s): the package and the mutex. -/
def memStorLock (ms : Loc) (γs : MemStorNames) : IProp GF :=
  iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
    sync.isMutex (ms.[MemoryStorage, go!"Mutex"]) (memstorageInv ms γs))

instance memStorLock_persistent (ms : Loc) (γs : MemStorNames) :
    Persistent (memStorLock (GF := GF) ms γs) := by
  unfold memStorLock; infer_instance

/-! ### The justification invariant -/

/-- The namespace of the storages' justification invariants. -/
def memStorN : Namespace := nroot.@"raft_memstor"

/-- **The stored snapshot at home**: the home's key, the `snapshot` field and the object, owned,
a quarter of its ghost value, and its validity (`J.SV`, `J.DL` at its index) unless it is
empty. -/
def memSnapHome (ms : Loc) (γs : MemStorNames) (J : MemJust GF) : IProp GF :=
  iprop(memKey γs.hk ∗ ∃ (sp : Loc) (sv : SnapshotM),
    ms.[MemoryStorage, go!"snapshot"] ↦ sp ∗ ownSnapM sp (DFrac.own 1) sv ∗
    ghostVar γs.sx memQ sv ∗
    (⌜sv.Metadata'.Index' = W64 0⌝ ∨ J.SV sv ∗ J.DL (uint.nat sv.Metadata'.Index')))

/-- The justification invariant's body: the justified compaction points (the authority of `jc`,
each element's `J.B`), and the snapshot at home or out with the lock's key. -/
def memJustInv (ms : Loc) (γs : MemStorNames) (J : MemJust GF) : IProp GF :=
  iprop((∃ (L : List Nat), monoListAuthOwn γs.jc 1 L ∗ [∗list] k ∈ L, J.B k) ∗
    (memSnapHome ms γs J ∨ memKey γs.lk))

/-- **The storage's invariant at the justifications `J`** (G1, generic: step 4's
`memStorInv ms γs γ id` is this at the API's `J`; persistent): the lock, the justification of the
compaction point `0`, and the justification invariant. -/
def memStorInvP (ms : Loc) (γs : MemStorNames) (J : MemJust GF) : IProp GF :=
  iprop(memStorLock ms γs ∗ J.B 0 ∗ inv memStorN (memJustInv ms γs J))

instance memStorInvP_persistent (ms : Loc) (γs : MemStorNames) (J : MemJust GF) :
    Persistent (memStorInvP ms γs J) := by
  unfold memStorInvP; infer_instance

/-- **The allocation's fuel** (`NewMemoryStorage`'s, consumed by `memStorInvP_alloc`): the
authority of `jc` (at `[0]`), and the snapshot's home, empty, which the lock does not hold. Also
what `InitialState`, which reads the snapshot without the lock, takes. -/
def memStorFresh (ms : Loc) (γs : MemStorNames) : IProp GF :=
  iprop(monoListAuthOwn γs.jc 1 [0] ∗ memKey γs.hk ∗ ∃ (sp : Loc),
    ms.[MemoryStorage, go!"snapshot"] ↦ sp ∗ ownSnapM sp (DFrac.own 1) memSnapEmpty ∗
    ghostVar γs.sx memQ memSnapEmpty)

/-- **The allocation of the storage's invariant** at the justifications `J` (step 4: at the
client's `(γ, id)`), from the fuel and the justification of `0`. -/
theorem memStorInvP_alloc (ms : Loc) (γs : MemStorNames) (J : MemJust GF) (E : CoPset) :
    ⊢ memStorLock ms γs -∗ memStorFresh ms γs -∗ J.B 0 ={E}=∗ memStorInvP ms γs J := by
  iintro #Hl Hf #HB0
  iunfold memStorFresh at Hf
  icases Hf with ⟨Ha, Hhk, %sp, Hsp, Hsnap, Hsx⟩
  imod inv_alloc memStorN E (memJustInv ms γs J) $$ [Ha Hhk Hsp Hsnap Hsx] with #Hinv
  · inext
    iunfold memJustInv
    isplitl [Ha]
    · iexists [0]
      iframe Ha
      iapply (BigSepL.bigSepL_singleton (Φ := fun _ k => J.B k)).2
      iexact HB0
    ileft
    iunfold memSnapHome
    iframe Hhk
    iexists sp, memSnapEmpty
    iframe
    ileft; ipureintro; rfl
  imodintro
  iunfold memStorInvP
  iframe Hl HB0 Hinv

/-- **The compaction's justification** (the contract's `storCompacted_bound`). -/
theorem memCompacted_bound (ms : Loc) (γs : MemStorNames) (J : MemJust GF) (c : Nat) :
    ⊢ memStorInvP ms γs J -∗ memCompacted γs c ={⊤}=∗ memBnd J c := by
  iintro #Hi #Hc
  iunfold memStorInvP at Hi
  icases Hi with ⟨#Hl, #HB0, #Hinv⟩
  iunfold memCompacted at Hc
  icases Hc with (%H | ⟨-, %L, #Hlb, %HL⟩)
  · subst H
    imodintro
    iunfold memBnd
    iexists 0
    iframe HB0
    ipureintro; exact Nat.le_refl 0
  obtain ⟨k, hk, hck⟩ := HL
  iinv Hinv with Hi Hclose
  iunfold memJustInv at Hi
  icases Hi with ⟨⟨%L', >Ha, >#Hall⟩, Hs⟩
  icases mono_list_auth_lb_valid _ _ _ _ $$ Ha Hlb with %Hv
  have hk' : k ∈ L' := Hv.2.subset hk
  ihave ⟨#Hk, -⟩ := BigSepL.bigSepL_mem_acc (Φ := fun k => J.B k) hk' $$ Hall
  imod Hclose $$ [Ha Hs] with -
  · inext
    iunfold memJustInv
    iframe Hs
    iexists L'
    iframe Ha Hall
  imodintro
  iunfold memBnd
  iexists k
  iframe Hk
  ipureintro; exact hck

/-- **Register a justified compaction point** (`Compact`, `ApplySnapshot`, under the lock). -/
theorem memCompJust_register (ms : Loc) (γs : MemStorNames) (J : MemJust GF) (k : Nat) (E : CoPset)
    (hE : ↑memStorN ⊆ E) :
    ⊢ memStorInvP ms γs J -∗ J.B k ={E}=∗ memCompJust γs k := by
  iintro #Hi #Hk
  iunfold memStorInvP at Hi
  icases Hi with ⟨#Hl, #HB0, #Hinv⟩
  iinv Hinv with Hi Hclose
  iunfold memJustInv at Hi
  icases Hi with ⟨⟨%L, >Ha, >#Hall⟩, Hs⟩
  imod monoListAuthOwn_update_app [k] $$ Ha with ⟨Ha, #Hlb⟩
  imod Hclose $$ [Ha Hs] with -
  · inext
    iunfold memJustInv
    iframe Hs
    iexists L ++ [k]
    iframe Ha
    iapply BigSepL.bigSepL_snoc.2
    iframe Hall Hk
  imodintro
  iunfold memCompJust
  iexists L ++ [k]
  iframe Hlb
  ipureintro; simp

/-- **Take the snapshot out of its home** with the lock's key: the snapshot under a later (the
next program step strips it: its validity need not be timeless). -/
theorem memSnap_take (ms : Loc) (γs : MemStorNames) (J : MemJust GF) (E : CoPset)
    (hE : ↑memStorN ⊆ E) :
    ⊢ memStorInvP ms γs J -∗ memKey γs.lk ={E}=∗ ▷ memSnapHome ms γs J := by
  iintro #Hi Hlk
  iunfold memStorInvP at Hi
  icases Hi with ⟨#Hl, #HB0, #Hinv⟩
  iinv Hinv with Hi Hclose
  iunfold memJustInv at Hi
  icases Hi with ⟨Hj, Hs⟩
  icases Hs with (Hh | >Hlk')
  · imod Hclose $$ [Hj Hlk] with -
    · inext
      iunfold memJustInv
      iframe Hj
      iright; iexact Hlk
    imodintro
    iexact Hh
  · iexfalso
    iapply memKey_excl $$ Hlk Hlk'

/-- **Put the snapshot back home**: the lock's key comes back. -/
theorem memSnap_put (ms : Loc) (γs : MemStorNames) (J : MemJust GF) (E : CoPset)
    (hE : ↑memStorN ⊆ E) :
    ⊢ memStorInvP ms γs J -∗ memSnapHome ms γs J ={E}=∗ memKey γs.lk := by
  iintro #Hi Hh
  iunfold memStorInvP at Hi
  icases Hi with ⟨#Hl, #HB0, #Hinv⟩
  iinv Hinv with Hi Hclose
  iunfold memJustInv at Hi
  icases Hi with ⟨Hj, Hs⟩
  icases Hs with (Hh' | >Hlk)
  · iunfold memSnapHome at Hh
    icases Hh with ⟨Hk, -⟩
    iunfold memSnapHome at Hh'
    icases Hh' with ⟨>Hk', -⟩
    iexfalso
    iapply memKey_excl $$ Hk Hk'
  imod Hclose $$ [Hj Hh] with -
  · inext
    iunfold memJustInv
    iframe Hj
    ileft; iexact Hh
  imodintro
  iexact Hlk

/-- The stored snapshot's ghost value: the client's half and the lock's and home's quarters
together move to `sv'`. -/
theorem memSnap_update (γs : MemStorNames) (a b c sv' : SnapshotM) :
    ⊢ ghostVar (GF := GF) γs.sx (1 : Qp).half a -∗ ghostVar γs.sx memQ b -∗
      ghostVar γs.sx memQ c ==∗
      ghostVar γs.sx (1 : Qp).half sv' ∗ ghostVar γs.sx memQ sv' ∗ ghostVar γs.sx memQ sv' := by
  iintro Ha Hb Hc
  icases ghostVar_agree γs.sx b _ c _ $$ Hb Hc with %Hbc
  subst Hbc
  ihave Hbc := (ghostVar_split_half γs.sx (1 : Qp).half b).2 $$ [Hb Hc]
  · iframe
  imod ghostVar_update_halves sv' γs.sx a b $$ Ha Hbc with ⟨Ha, Hbc⟩
  icases (ghostVar_split_half γs.sx (1 : Qp).half sv').1 $$ Hbc with ⟨Hb, Hc⟩
  imodintro
  isplitl [Ha]
  · iexact Ha
  isplitl [Hb]
  · iexact Hb
  iexact Hc

/-- The client's half agrees with a quarter. -/
theorem memSnapExact_agree (γs : MemStorNames) (a b : SnapshotM) :
    ⊢ memSnapExact (GF := GF) γs a -∗ ghostVar γs.sx memQ b -∗ ⌜a = b⌝ := by
  iintro Ha Hb
  iunfold memSnapExact at Ha
  iapply ghostVar_agree γs.sx a _ b _ $$ Ha Hb

/-- The rest of a `MemoryStorage`: its hard state `hs`, which `InitialState` reads without the
lock, and the `initialState` counter it increments without it (the other half of `hardState` is
the lock's). The application's; `SetHardState` needs nothing else. -/
def memStorMeta (ms : Loc) (γs : MemStorNames) (hs : HardStateM) : IProp GF :=
  iprop(∃ (n : w64) (hp : Loc),
  "#Hinit" ∷ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
  "#Hmu" ∷ sync.isMutex (ms.[MemoryStorage, go!"Mutex"]) (memstorageInv ms γs) ∗
  "HhardState" ∷ ms.[MemoryStorage, go!"hardState"] ↦{DFrac.own (1 : Qp).half} hp ∗
  "#Hhs" ∷ hsOpt hp hs ∗
  "Hcs_initialState" ∷
    (ms.[MemoryStorage, go!"callStats"]).[inMemStorageCallStats, go!"initialState"] ↦ n)

/-- `CreateSnapshot`'s `cs` argument: `nil` (`oc = none`, the stored `ConfState` kept) or a
`ConfState` at any fraction. -/
def memCsArg (cs : Loc) (dq : DFrac) (oc : Option ConfStateM) : IProp GF :=
  match oc with
  | none => iprop(⌜cs = null⌝)
  | some c => ownCSM cs dq c

end proof

end EtcdGrove
end Perennial
