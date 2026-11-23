/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/treemap/Defs.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The model of `gods/maps/treemap` (the lab's sorted-slice model, `harness/rpcmodel/gods`), the
subset SwiftPaxos's `state` uses: its abstract state and representation predicate.

* Keys are `int64`s (`state.Key`) behind `interface{}` values given by an encoding `enc`
  (`interface.mkOk state.Key.ty #k` for `state`); the comparator `cmp` meets `cmpOk cmp enc`:
  on two encoded keys it returns an `int` whose sign is the signed comparison of the keys.
* `isTreeMap tm enc es`: the `*Map` at `tm` holds the entries `es` (key, value interface),
  strictly increasing by key (`sortedE`); its `entries` slice and its capacity are owned.
* `lookupE es k`, `putE es k v`: the map operations on the entry list.
-/
module

public import Perennial.Proof.ProofPrelude
public import Dsverify.GeneratedProof.github_com.emirpasic.gods.maps.treemap

@[expose] public section

noncomputable section

namespace Perennial.github_com.emirpasic.gods.maps.treemap

open Iris Iris.BI Iris.ProgramLogic Iris.Std

variable [GooseExts]

/-! ## The pure model -/

/-- Entries: key, value. -/
abbrev Entries := List (w64 × GoInterface)

/-- Strictly increasing keys (signed). -/
def sortedE (es : Entries) : Prop := es.Pairwise (fun a b => sint.Z a.1 < sint.Z b.1)

/-- The value of `k`, if any. -/
def lookupE (es : Entries) (k : w64) : Option GoInterface :=
  (es.find? (fun e => decide (e.1 = k))).map Prod.snd

/-- The position of the first entry whose key is not below `k`. -/
def idxOf (es : Entries) (k : w64) : Nat :=
  (es.takeWhile (fun e => decide (sint.Z e.1 < sint.Z k))).length

/-- `Put(k, v)`: replace `k`'s entry, or insert one in order. -/
def putE (es : Entries) (k : w64) (v : GoInterface) : Entries :=
  if (es[idxOf es k]?).map Prod.fst = some k then es.set (idxOf es k) (k, v)
  else es.take (idxOf es k) ++ (k, v) :: es.drop (idxOf es k)

/-- The Go entry of an abstract one. -/
def toEntry (enc : w64 → GoInterface) (e : w64 × GoInterface) : entry :=
  entry.mk (enc e.1) e.2

/-! ## Pure lemmas -/

theorem idxOf_le (es : Entries) (k : w64) : idxOf es k ≤ es.length := by
  unfold idxOf; exact (List.takeWhile_sublist _).length_le

theorem lt_of_lt_idxOf (es : Entries) (k : w64) (j : Nat) (e : w64 × GoInterface)
    (hj : j < idxOf es k) (he : es[j]? = some e) : sint.Z e.1 < sint.Z k := by
  unfold idxOf at hj
  induction es generalizing j with
  | nil => simp at hj
  | cons a es ih =>
    by_cases hak : sint.Z a.1 < sint.Z k
    · simp [List.takeWhile_cons, hak] at hj
      cases j with
      | zero => simp at he; subst he; exact hak
      | succ j => exact ih j (by omega) (by simpa using he)
    · simp [List.takeWhile_cons, hak] at hj

/-- `idxOf` is characterized by: every entry before it is below `k`, the one at it (if any)
is not. -/
theorem idxOf_eq (es : Entries) (k : w64) (i : Nat) (hi : i ≤ es.length)
    (hlt : ∀ j e, j < i → es[j]? = some e → sint.Z e.1 < sint.Z k)
    (hge : ∀ e, es[i]? = some e → ¬ sint.Z e.1 < sint.Z k) : idxOf es k = i := by
  unfold idxOf
  induction es generalizing i with
  | nil => simp at hi ⊢; omega
  | cons a es ih =>
    cases i with
    | zero =>
      have := hge a (by simp)
      simp [List.takeWhile_cons, this]
    | succ i =>
      have ha := hlt 0 a (by omega) (by simp)
      simp only [List.takeWhile_cons, ha, decide_true, ite_true, List.length_cons]
      congr 1
      apply ih i (by simp at hi; omega)
      · intro j e hj he; exact hlt (j + 1) e (by omega) (by simpa using he)
      · intro e he; exact hge e (by simpa using he)

theorem sortedE_cons (a : w64 × GoInterface) (es : Entries) :
    sortedE (a :: es) ↔ (∀ b ∈ es, sint.Z a.1 < sint.Z b.1) ∧ sortedE es := by
  unfold sortedE; exact List.pairwise_cons

/-- In a sorted list, `lookupE` finds `k` only at `idxOf`. -/
theorem lookupE_idx (es : Entries) (k : w64) (hs : sortedE es) :
    lookupE es k = match es[idxOf es k]? with
      | some e => if e.1 = k then some e.2 else none
      | none => none := by
  induction es with
  | nil => simp [lookupE, idxOf]
  | cons a es ih =>
    rw [sortedE_cons] at hs
    by_cases hak : sint.Z a.1 < sint.Z k
    · have hne : a.1 ≠ k := by intro h; rw [h] at hak; omega
      have : idxOf (a :: es) k = idxOf es k + 1 := by
        simp [idxOf, List.takeWhile_cons, hak]
      rw [this]
      simp only [List.getElem?_cons_succ]
      rw [← ih hs.2]
      simp [lookupE, List.find?_cons, hne]
    · have : idxOf (a :: es) k = 0 := by simp [idxOf, List.takeWhile_cons, hak]
      rw [this]
      simp only [List.getElem?_cons_zero]
      by_cases hak' : a.1 = k
      · simp [lookupE, List.find?_cons, hak']
      · simp only [hak', if_false]
        -- every later key is above `a.1 ≥ k`, so differs from `k`
        have hnone : ∀ b ∈ es, b.1 ≠ k := by
          intro b hb hbk
          have := hs.1 b hb
          rw [hbk] at this
          have : sint.Z a.1 ≠ sint.Z k := by
            intro h; apply hak'; exact BitVec.eq_of_toInt_eq h
          omega
        simp only [lookupE, List.find?_cons, hak', decide_false]
        rw [List.find?_eq_none.mpr (by intro b hb; simpa using hnone b hb)]
        rfl

theorem not_lt_at_idxOf (es : Entries) (k : w64) (h : idxOf es k < es.length) :
    ¬ sint.Z (es[idxOf es k]'h).1 < sint.Z k := by
  induction es with
  | nil => simp at h
  | cons a es ih =>
    by_cases hak : sint.Z a.1 < sint.Z k
    · have he : idxOf (a :: es) k = idxOf es k + 1 := by simp [idxOf, List.takeWhile_cons, hak]
      have h' : idxOf es k < es.length := by rw [he] at h; simp at h; omega
      have := ih h'
      simp only [he, List.getElem_cons_succ]; exact this
    · have he : idxOf (a :: es) k = 0 := by simp [idxOf, List.takeWhile_cons, hak]
      simp only [he, List.getElem_cons_zero]; exact hak

theorem insert_shift {A : Type} (L : List A) (z new : A) (idx : Nat) (h : idx ≤ L.length) :
    (List.take (idx + 1) (L ++ [z]) ++
        (List.take (L.length + 1 - (idx + 1)) (subslice idx (L.length + 1) (L ++ [z])) ++
          List.drop (L.length + 1 - idx) (subslice (idx + 1) (L.length + 1) (L ++ [z]))) ++
      List.drop (L.length + 1) (L ++ [z])).set idx new = L.take idx ++ new :: L.drop idx := by
  have hX : (L ++ [z]).take (L.length + 1) = L ++ [z] := List.take_of_length_le (by simp)
  simp only [subslice, hX]
  have h1 : List.drop (L.length + 1) (L ++ [z]) = [] := List.drop_of_length_le (by simp)
  have h2 : List.drop (L.length + 1 - idx) (List.drop (idx + 1) (L ++ [z])) = [] :=
    List.drop_of_length_le (by simp; omega)
  have h3 : List.take (L.length + 1 - (idx + 1)) (List.drop idx (L ++ [z])) = L.drop idx := by
    rw [List.drop_append_of_le_length h]
    rw [List.take_append_of_le_length (by simp)]
    exact List.take_of_length_le (by simp)
  rw [h1, h2, h3]
  simp only [List.append_nil]
  rw [List.take_add_one]
  rw [List.take_append_of_le_length h]
  rw [List.append_assoc, List.set_append_right _ _ (by simp; omega)]
  simp only [List.length_take, Nat.min_eq_left h, Nat.sub_self]
  cases hg : (L ++ [z])[idx]? with
  | none => simp at hg; omega
  | some y => simp

theorem putE_found (es : Entries) (k : w64) (v : GoInterface)
    (h : (es[idxOf es k]?).map Prod.fst = some k) : putE es k v = es.set (idxOf es k) (k, v) := by
  unfold putE; rw [if_pos h]

theorem putE_notfound (es : Entries) (k : w64) (v : GoInterface)
    (h : ¬ (es[idxOf es k]?).map Prod.fst = some k) :
    putE es k v = es.take (idxOf es k) ++ (k, v) :: es.drop (idxOf es k) := by
  unfold putE; rw [if_neg h]

theorem sortedE_iff (es : Entries) :
    sortedE es ↔ ∀ (a b : Nat) (ha : a < es.length) (hb : b < es.length), a < b →
      sint.Z es[a].1 < sint.Z es[b].1 := by
  unfold sortedE; rw [List.pairwise_iff_getElem]

theorem sortedE_putE (es : Entries) (k : w64) (v : GoInterface) (hs : sortedE es) :
    sortedE (putE es k v) := by
  have hsi := (sortedE_iff es).mp hs
  by_cases h : (es[idxOf es k]?).map Prod.fst = some k
  · rw [putE_found es k v h, sortedE_iff]
    have hlt : idxOf es k < es.length := by
      rcases Nat.lt_or_ge (idxOf es k) es.length with h' | h'
      · exact h'
      · rw [List.getElem?_eq_none h'] at h; cases h
    have hk : es[idxOf es k].1 = k := by
      rw [List.getElem?_eq_getElem hlt] at h; simpa using h
    intro a b ha hb hab
    simp only [List.length_set] at ha hb
    simp only [List.getElem_set]
    have := hsi a b ha hb hab
    split <;> split <;> (try subst_vars) <;> simp_all <;> omega
  · rw [putE_notfound es k v h]
    obtain ⟨i, hi⟩ : ∃ i, i = idxOf es k := ⟨_, rfl⟩
    rw [← hi]
    have hile : i ≤ es.length := hi ▸ idxOf_le es k
    -- every key before `i` is below `k`, every key from `i` on above it
    have hbefore : ∀ j (hj : j < i), sint.Z (es[j]'(by omega)).1 < sint.Z k := fun j hj =>
      lt_of_lt_idxOf es k j _ (hi ▸ hj) (List.getElem?_eq_getElem _)
    have hafter : ∀ j (hj : j < es.length), i ≤ j → sint.Z k < sint.Z es[j].1 := by
      intro j hj hij
      have hil : i < es.length := by omega
      have hnot : ¬ sint.Z es[i].1 < sint.Z k := by subst hi; exact not_lt_at_idxOf es k hil
      have hne : es[i].1 ≠ k := by
        intro he; apply h; rw [← hi, List.getElem?_eq_getElem hil]; simp [he]
      have hki : sint.Z k < sint.Z es[i].1 := by
        have : sint.Z es[i].1 ≠ sint.Z k := fun h' => hne (BitVec.eq_of_toInt_eq h')
        omega
      rcases Nat.eq_or_lt_of_le hij with he | he
      · subst he; exact hki
      · have := hsi i j hil hj he; omega
    have htd : (es.take i ++ es.drop i).Pairwise (fun a b => sint.Z a.1 < sint.Z b.1) := by
      rw [List.take_append_drop]; exact hs
    rw [List.pairwise_append] at htd
    unfold sortedE
    rw [List.pairwise_append, List.pairwise_cons]
    have hdrop : ∀ b ∈ es.drop i, sint.Z k < sint.Z b.1 := by
      intro b hb
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hb
      rw [List.getElem_drop]
      simp only [List.length_drop] at hj
      exact hafter _ (by omega) (by omega)
    have htake : ∀ a ∈ es.take i, sint.Z a.1 < sint.Z k := by
      intro a ha
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ha
      rw [List.getElem_take]
      simp only [List.length_take] at hj
      exact hbefore j (by omega)
    refine ⟨htd.1, ⟨hdrop, htd.2.1⟩, ?_⟩
    intro a ha b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact htake a ha
    · exact htd.2.2 a ha b hb


theorem lookupE_cons (a : w64 × GoInterface) (es : Entries) (k : w64) :
    lookupE (a :: es) k = if a.1 = k then some a.2 else lookupE es k := by
  unfold lookupE; by_cases h : a.1 = k <;> simp [h]

theorem lookupE_some_iff (es : Entries) (k : w64) (x : GoInterface) (hs : sortedE es) :
    lookupE es k = some x ↔ (k, x) ∈ es := by
  induction es with
  | nil => simp [lookupE]
  | cons a es ih =>
    rw [sortedE_cons] at hs
    rw [lookupE_cons, List.mem_cons]
    by_cases h : a.1 = k
    · simp only [h, ite_true, Option.some.injEq]
      constructor
      · intro hx; left; subst hx; rw [← h]
      · rintro (he | hm)
        · rw [← he]
        · have := hs.1 _ hm; simp only at this; rw [h] at this; omega
    · simp only [h, ite_false, ih hs.2]
      constructor
      · intro hm; right; exact hm
      · rintro (he | hm)
        · exfalso; apply h; rw [← he]
        · exact hm

theorem mem_putE (es : Entries) (k : w64) (x : GoInterface) (hs : sortedE es) (k' : w64)
    (x' : GoInterface) :
    (k', x') ∈ putE es k x ↔ (k' = k ∧ x' = x) ∨ ((k', x') ∈ es ∧ k' ≠ k) := by
  have hsi := (sortedE_iff es).mp hs
  by_cases h : (es[idxOf es k]?).map Prod.fst = some k
  · rw [putE_found es k x h]
    have hlt : idxOf es k < es.length := by
      rcases Nat.lt_or_ge (idxOf es k) es.length with h' | h'
      · exact h'
      · rw [List.getElem?_eq_none h'] at h; cases h
    have hk : es[idxOf es k].1 = k := by
      rw [List.getElem?_eq_getElem hlt] at h; simpa using h
    rw [List.mem_iff_getElem, List.mem_iff_getElem]
    constructor
    · rintro ⟨j, hj, hje⟩
      simp only [List.length_set] at hj
      rw [List.getElem_set] at hje
      split at hje
      · left; cases hje; exact ⟨rfl, rfl⟩
      · right
        refine ⟨⟨j, hj, hje⟩, ?_⟩
        intro hkk
        have : es[j].1 = es[idxOf es k].1 := by rw [hje, hk]; exact hkk
        rcases Nat.lt_or_gt_of_ne (Ne.symm ‹¬idxOf es k = j›) with hl | hl
        · have h2 := hsi j _ hj hlt hl; rw [this] at h2; omega
        · have h2 := hsi _ j hlt hj hl; rw [this] at h2; omega
    · rintro (⟨rfl, rfl⟩ | ⟨⟨j, hj, hje⟩, hne⟩)
      · exact ⟨idxOf es k', by simp [hlt], by simp⟩
      · have hji : j ≠ idxOf es k := by
          intro e; subst e; apply hne; rw [← hk, hje]
        exact ⟨j, by simp [hj], by rw [List.getElem_set]; simp [Ne.symm hji, hje]⟩
  · rw [putE_notfound es k x h]
    -- no entry of `es` has key `k`
    have hnone : ∀ e ∈ es, e.1 ≠ k := by
      intro e he hek
      have : lookupE es k = some e.2 := (lookupE_some_iff es k e.2 hs).mpr (by rw [← hek]; exact he)
      rw [lookupE_idx es k hs] at this
      apply h
      revert this
      cases es[idxOf es k]? with
      | none => simp
      | some e' => simp only; split <;> simp_all
    simp only [List.mem_append, List.mem_cons]
    constructor
    · rintro (hm | he | hm)
      · right; have hm' := List.mem_of_mem_take hm; exact ⟨hm', hnone _ hm'⟩
      · left; cases he; exact ⟨rfl, rfl⟩
      · right; have hm' := List.mem_of_mem_drop hm; exact ⟨hm', hnone _ hm'⟩
    · rintro (⟨rfl, rfl⟩ | ⟨hm, _⟩)
      · right; left; rfl
      · rw [← List.take_append_drop (idxOf es k) es, List.mem_append] at hm
        rcases hm with hm | hm
        · left; exact hm
        · right; right; exact hm

theorem lookupE_putE (es : Entries) (k : w64) (x : GoInterface) (hs : sortedE es) (k' : w64) :
    lookupE (putE es k x) k' = if k' = k then some x else lookupE es k' := by
  have hs' := sortedE_putE es k x hs
  apply Option.ext
  intro x'
  rw [lookupE_some_iff _ _ _ hs', mem_putE es k x hs]
  by_cases hk : k' = k
  · subst hk; simp only [ite_true, Option.some.injEq, true_and, ne_eq, not_true_eq_false,
      and_false, or_false]; exact eq_comm
  · simp only [hk, ite_false, false_and, false_or, ne_eq, not_false_eq_true, and_true]
    exact (lookupE_some_iff es k' x' hs).symm

end Perennial.github_com.emirpasic.gods.maps.treemap
