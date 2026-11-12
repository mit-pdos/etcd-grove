/-
Lean-first (no Rocq counterpart).

# The tester's Go values as its Lean records (WAL W4c step 3)

The representation predicates the specs of the tester's functions are written in:

* an entry slice is read-only once built (`↦*□`): an operation's entries are shared by every copy
  of the operation (`copyOps` copies the slice headers);
* an operation (`walOp`) is its fields and its entries (`opRep`, persistent);
* an operation slice is read-only too (`opsRep`): the candidates' histories and the images are
  never written once built, and the history `since` is only appended to (the append writes past
  the persistent elements, into the capacity the oracle owns: `wp_slice_append_persistent`);
* the oracle (`oracleRep`) owns its candidate slice (whose bounds are written in place) and the
  capacities of the slices it appends to.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.etcd.wal

section pure
variable [GooseExts]

instance THs_decEq : DecidableEq THs := fun a b =>
  decidable_of_iff (a.term' = b.term' ∧ a.vote' = b.vote' ∧ a.commit' = b.commit')
    (by cases a; cases b; simp)

instance TEnt_decEq : DecidableEq TEnt := fun a b =>
  decidable_of_iff (a.index' = b.index' ∧ a.term' = b.term' ∧ a.size' = b.size' ∧ a.salt' = b.salt')
    (by cases a; cases b; simp)

instance TOp_decEq : DecidableEq TOp := fun a b =>
  decidable_of_iff (a.snap = b.snap ∧ a.hs = b.hs ∧ a.ents = b.ents ∧ a.idx = b.idx ∧ a.term = b.term)
    (by cases a; cases b; simp)

instance TContents_decEq : DecidableEq TContents := fun a b =>
  decidable_of_iff (a.hs = b.hs ∧ a.baseIdx = b.baseIdx ∧ a.baseTerm = b.baseTerm ∧ a.ents = b.ents)
    (by cases a; cases b; simp)

/-- Two lists of equal length agreeing on their first `i` elements and differing at `i` differ. -/
theorem list_ne_of_getElem {α : Type} {l1 l2 : List α} {i : Nat} {x y : α} (h1 : l1[i]? = some x)
    (h2 : l2[i]? = some y) (hne : x ≠ y) : l1 ≠ l2 := by
  rintro rfl; rw [h1] at h2; exact hne (Option.some.inj h2)

/-- Two lists of equal length that agree on every prefix element agree. -/
theorem list_take_succ_eq {α : Type} {l1 l2 : List α} {i : Nat} {x : α} (h1 : l1[i]? = some x)
    (h2 : l2[i]? = some x) (h : l1.take i = l2.take i) : l1.take (i + 1) = l2.take (i + 1) := by
  rw [List.take_add_one, List.take_add_one, h1, h2, h]

end pure

section rep
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.wal.Assumptions]

theorem val_false_ne_true : (#false : val) ≠ #true := fun h => by
  cases GoGlobalContext.intoVal_inj_bool h

theorem val_true_ne_false : (#true : val) ≠ #false := fun h => by
  cases GoGlobalContext.intoVal_inj_bool h

/-- A postcondition at a value computed in the proof: `HΦ` at any `y` equal to the spec's `x` (so
each branch of a proof returns its own expression of the value and proves it equal). -/
theorem ret_gen {V : Type} (Φ : val → IProp GF) (x : V) (P : IProp GF) :
    (P -∗ Φ #x) ⊢ ∀ y : V, ⌜y = x⌝ ∗ P -∗ Φ #y := by
  iintro H %y ⟨%hy, HP⟩
  subst hy
  iapply H $$ HP

/-- The Go operation `v` is `o`: its fields, and its entries (read-only). -/
def opRep (v : walOp) (o : TOp) : IProp GF :=
  iprop(⌜v.snap' = o.snap ∧ v.hs' = o.hs ∧ v.idx' = o.idx ∧ v.term' = o.term⌝ ∗ v.ents' ↦*□ o.ents)

instance opRep_persistent (v : walOp) (o : TOp) : Persistent (opRep (GF := GF) v o) := by
  unfold opRep; infer_instance

/-- The Go values `vs` are the operations `h`, element by element. -/
def opsElems (vs : List walOp) (h : List TOp) : IProp GF :=
  iprop(⌜vs.length = h.length⌝ ∗ □ ∀ (i : Nat) (v : walOp) (o : TOp),
    ⌜vs[i]? = some v ∧ h[i]? = some o⌝ -∗ opRep v o)

instance opsElems_persistent (vs : List walOp) (h : List TOp) :
    Persistent (opsElems (GF := GF) vs h) := by
  unfold opsElems; infer_instance

theorem opsElems_length (vs : List walOp) (h : List TOp) :
    opsElems (GF := GF) vs h ⊢ ⌜vs.length = h.length⌝ := by
  unfold opsElems
  iintro ⟨%hl, -⟩; ipureintro; exact hl

/-- The `i`-th Go operation is the `i`-th operation. -/
theorem opsElems_lookup (vs : List walOp) (h : List TOp) (i : Nat) (v : walOp)
    (hv : vs[i]? = some v) :
    opsElems (GF := GF) vs h ⊢ ∃ o, ⌜h[i]? = some o⌝ ∗ opRep v o := by
  unfold opsElems
  iintro ⟨%hl, #Hall⟩
  have hi : i < h.length := by rw [← hl]; exact (List.getElem?_eq_some_iff.1 hv).1
  iexists h[i]
  isplitr
  · ipureintro; exact List.getElem?_eq_getElem hi
  iapply Hall
  ipureintro; exact ⟨hv, List.getElem?_eq_getElem hi⟩

/-- Appending an operation. -/
theorem opsElems_snoc (vs : List walOp) (h : List TOp) (v : walOp) (o : TOp) :
    opsElems (GF := GF) vs h ∗ opRep v o ⊢ opsElems (vs ++ [v]) (h ++ [o]) := by
  unfold opsElems
  iintro ⟨⟨%hl, #Hall⟩, #Ho⟩
  isplitr
  · ipureintro; simp [hl]
  imodintro
  iintro %i %v' %o' %hi
  obtain ⟨h1, h2⟩ := hi
  by_cases hlt : i < vs.length
  · rw [List.getElem?_append_left hlt] at h1
    rw [List.getElem?_append_left (by omega)] at h2
    iapply Hall; ipureintro; exact ⟨h1, h2⟩
  · rw [List.getElem?_append_right (by omega)] at h1
    rw [List.getElem?_append_right (by omega)] at h2
    have : i - vs.length = 0 := by
      have := (List.getElem?_eq_some_iff.1 h1).1; simp at this; omega
    rw [this] at h1
    rw [show i - h.length = 0 by omega] at h2
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h1 h2
    subst h1 h2
    iexact Ho

theorem opsElems_nil : ⊢ opsElems (GF := GF) [] [] := by
  unfold opsElems
  iintro
  isplitr
  · ipureintro; rfl
  imodintro
  iintro %i %v %o %h
  simp at h

theorem opsElems_subslice (vs : List walOp) (h : List TOp) (lo hi : Nat) :
    opsElems (GF := GF) vs h ⊢ opsElems (subslice lo hi vs) (subslice lo hi h) := by
  unfold opsElems
  iintro ⟨%hl, #Hall⟩
  isplitr
  · ipureintro; simp [subslice, hl]
  imodintro
  iintro %i %v %o %hi
  obtain ⟨h1, h2⟩ := hi
  simp only [subslice, List.getElem?_drop, List.getElem?_take] at h1 h2
  split at h1
  · split at h2
    · iapply Hall; ipureintro; exact ⟨h1, h2⟩
    · exfalso; omega
  · cases h1

/-- The operation slice `s` is `h` (read-only). -/
def opsRep (s : GoSlice) (h : List TOp) : IProp GF :=
  iprop(∃ vs : List walOp, s ↦*□ vs ∗ opsElems vs h)

instance opsRep_persistent (s : GoSlice) (h : List TOp) : Persistent (opsRep (GF := GF) s h) := by
  unfold opsRep; infer_instance

/-- A subslice of an operation slice. -/
theorem opsRep_slice (s : GoSlice) (h : List TOp) (lo hi : w64)
    (hb : 0 ≤ sint.Z lo ∧ sint.Z lo ≤ sint.Z hi ∧ sint.Z hi ≤ sint.Z s.len) :
    opsRep (GF := GF) s h ⊢
      opsRep (slice.slice s walOp lo hi) (subslice (sint.nat lo) (sint.nat hi) h) := by
  unfold opsRep
  iintro ⟨%vs, Hs, #Hel⟩
  icases (ownSlice_slice lo hi s DFrac.discard vs hb).1 $$ Hs with ⟨-, Hm, -⟩
  iexists _
  iframe
  iapply opsElems_subslice
  iexact Hel

/-- The Go candidate `v` is `c`. -/
def candRep (v : cand) (c : TCand) : IProp GF :=
  iprop(⌜v.unl' = c.unl ∧ v.pur' = c.pur⌝ ∗ opsRep v.h' c.h)

instance candRep_persistent (v : cand) (c : TCand) : Persistent (candRep (GF := GF) v c) := by
  unfold candRep; infer_instance

/-- The Go candidates `vs` are `cs`, element by element. -/
def candsElems (vs : List cand) (cs : List TCand) : IProp GF :=
  iprop(⌜vs.length = cs.length⌝ ∗ □ ∀ (i : Nat) (v : cand) (c : TCand),
    ⌜vs[i]? = some v ∧ cs[i]? = some c⌝ -∗ candRep v c)

instance candsElems_persistent (vs : List cand) (cs : List TCand) :
    Persistent (candsElems (GF := GF) vs cs) := by
  unfold candsElems; infer_instance

/-- The candidate slice `s` is `cs`, owned with its capacity (its elements' bounds are written in
place, and it is appended to). -/
def candsOwn (s : GoSlice) (cs : List TCand) : IProp GF :=
  iprop(∃ vs : List cand, s ↦* vs ∗ ownSliceCap cand s (DFrac.own 1) ∗ candsElems vs cs)

/-- The Go contents `v` are `c` (the entries read-only). -/
def contentsRep (v : contents) (c : TContents) : IProp GF :=
  iprop(⌜v.hs' = c.hs ∧ v.baseIdx' = c.baseIdx ∧ v.baseTerm' = c.baseTerm⌝ ∗ v.ents' ↦*□ c.ents)

instance contentsRep_persistent (v : contents) (c : TContents) :
    Persistent (contentsRep (GF := GF) v c) := by
  unfold contentsRep; infer_instance

/-- A read's result: the contents `c` and `true`, or `false` when the read fails (`none`). -/
def readRes (r : Option TContents) (v : contents) (ok : Bool) : IProp GF :=
  match r with
  | some c => iprop(⌜ok = true⌝ ∗ contentsRep v c)
  | none => iprop(⌜ok = false⌝)

/-- An entry step's result: the entries `x` (read-only) and `true`, or `false` (`none`). -/
def entsRes (r : Option (List TEnt)) (s : GoSlice) (ok : Bool) : IProp GF :=
  match r with
  | some x => iprop(⌜ok = true⌝ ∗ s ↦*□ x)
  | none => iprop(⌜ok = false⌝)

/-- **The Go oracle `v` is `o`**: the candidates owned, `since` read-only with its capacity, the
pending opens read-only with their capacity. -/
def oracleRep (v : oracle) (o : TOracle) : IProp GF :=
  iprop(⌜v.created' = o.created ∧ v.synced' = o.synced ∧ v.lastHS' = o.lastHS⌝ ∗
    candsOwn v.cands' o.cands ∗
    opsRep v.since' o.since ∗ ownSliceCap walOp v.since' (DFrac.own 1) ∗
    v.opens' ↦*□ o.opens ∗ ownSliceCap w64 v.opens' (DFrac.own 1))

end rep

end etcd_wal
end EtcdGrove
end Perennial
