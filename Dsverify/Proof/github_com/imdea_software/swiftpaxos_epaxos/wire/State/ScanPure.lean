/-
Pure lemmas for `Execute`'s `SCAN` case: the treemap's entries (signed-sorted keys) filtered by
the range predicate, in order, are `rangeKeys`' keys present in the store.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Interface.State

@[expose] public section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open github_com.imdea_software.swiftpaxos_epaxos.kvs

/-- Keys in increasing signed order (the lab's `TreemapLemmas`). -/
abbrev keysSorted (ks : List w64) : Prop := ks.Pairwise (fun a b => sint.Z a < sint.Z b)

/-- Two signed-sorted key lists with the same members are equal. -/
theorem keysSorted_ext : ∀ {l1 l2 : List w64}, keysSorted l1 → keysSorted l2 →
    (∀ x, x ∈ l1 ↔ x ∈ l2) → l1 = l2
  | [], [], _, _, _ => rfl
  | [], b :: _, _, _, h => absurd ((h b).mpr (List.mem_cons_self ..)) (by simp)
  | a :: _, [], _, _, h => absurd ((h a).mp (List.mem_cons_self ..)) (by simp)
  | a :: l1, b :: l2, h1, h2, h => by
    rw [keysSorted, List.pairwise_cons] at h1 h2
    have hab : a = b := by
      have ha := (h a).mp (List.mem_cons_self ..)
      have hb := (h b).mpr (List.mem_cons_self ..)
      rcases List.mem_cons.mp ha with e | ha
      · exact e
      rcases List.mem_cons.mp hb with e | hb
      · exact e.symm
      have := h1.1 b hb; have := h2.1 a ha; omega
    subst hab
    rw [keysSorted_ext h1.2 h2.2 (fun x => by
      constructor
      · intro hx
        have hx' := (h x).mp (List.mem_cons_of_mem _ hx)
        rcases List.mem_cons.mp hx' with e | e
        · subst e; have := h1.1 x hx; omega
        · exact e
      · intro hx
        have hx' := (h x).mpr (List.mem_cons_of_mem _ hx)
        rcases List.mem_cons.mp hx' with e | e
        · subst e; have := h2.1 x hx; omega
        · exact e)]

/-- Adding a small non-negative offset without signed overflow. -/
theorem sint_add_small (K : w64) (j : Nat) (h : sint.Z K + j < 2 ^ 63) :
    sint.Z (K + W64 (j : Int)) = sint.Z K + j := by
  word

/-- `rangeKeys`' body over its bounds `K` and `hi`. -/
def rangeL (K hi : w64) : List w64 :=
  if sint.Z K ≤ sint.Z hi then
    (List.range ((sint.Z hi - sint.Z K).toNat + 1)).map (fun j : Nat => K + W64 (j : Int))
  else []

theorem rangeKeys_eq (c : WCmd) : rangeKeys c = rangeL c.key (c.key + leToU64 (c.val.take 8)) :=
  rfl

theorem mem_rangeL (K hi x : w64) :
    x ∈ rangeL K hi ↔ sint.Z K ≤ sint.Z x ∧ sint.Z x ≤ sint.Z hi := by
  unfold rangeL
  have hhi : sint.Z hi < 2 ^ 63 := by word
  split
  · rename_i hle
    simp only [List.mem_map, List.mem_range]
    constructor
    · rintro ⟨j, hj, rfl⟩
      rw [sint_add_small K j (by omega)]
      omega
    · rintro ⟨h1, h2⟩
      refine ⟨(sint.Z x - sint.Z K).toNat, by omega, ?_⟩
      have e := sint_add_small K (sint.Z x - sint.Z K).toNat (by omega)
      rw [Int.toNat_of_nonneg (by omega)] at e
      have : sint.Z (K + W64 ((sint.Z x - sint.Z K).toNat : Int)) = sint.Z x := by
        rw [Int.toNat_of_nonneg (by omega)] at *; omega
      exact BitVec.toInt_inj.mp this
  · simp only [List.not_mem_nil, false_iff]; omega

theorem rangeL_sorted (K hi : w64) : keysSorted (rangeL K hi) := by
  unfold rangeL keysSorted
  split
  · rename_i hle
    have hhi : sint.Z hi < 2 ^ 63 := by word
    rw [List.pairwise_map]
    refine List.Pairwise.imp_of_mem ?_ List.pairwise_lt_range
    intro a b ha hb hab
    rw [List.mem_range] at ha hb
    rw [sint_add_small K a (by omega), sint_add_small K b (by omega)]
    omega
  · exact List.Pairwise.nil

theorem flatten_filterMap_getD {V : Type} (S : GMap w64 (List V)) (L : List w64) :
    (L.filterMap S.lookup).flatten = (L.map (fun k => (S.lookup k).getD [])).flatten := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    rw [List.filterMap_cons, List.map_cons, List.flatten_cons]
    cases h : S.lookup a with
    | none => simp only [Option.getD_none, List.nil_append]; exact ih
    | some v => simp only [Option.getD_some, List.flatten_cons]; rw [ih]

theorem flatten_map_filter_dom {V : Type} (S : GMap w64 (List V)) (L : List w64) :
    (L.map (fun k => (S.lookup k).getD [])).flatten =
      ((L.filter (fun k => (S.lookup k).isSome)).map (fun k => (S.lookup k).getD [])).flatten := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    rw [List.filter_cons]
    cases h : S.lookup a with
    | none => simp only [h, Option.isSome_none, List.map_cons, Option.getD_none,
        List.flatten_cons, List.nil_append]; exact ih
    | some v => simp only [h, Option.isSome_some, ite_true, List.map_cons, Option.getD_some,
        List.flatten_cons]; rw [ih]

/-- `Execute`'s `SCAN` result: the store's values at the treemap's keys (signed-sorted, the
store's domain) that lie in `[K, hi]`, in order, concatenated, are `rangeL K hi`'s present
values, concatenated. -/
theorem scan_flatten {V : Type} (S : GMap w64 (List V)) (ks : List w64) (hs : keysSorted ks)
    (hdom : ∀ k, k ∈ ks ↔ (S.lookup k).isSome) (K hi : w64) :
    ((ks.filter (fun k => decide (sint.Z K ≤ sint.Z k) && decide (sint.Z k ≤ sint.Z hi))).map
        (fun k => (S.lookup k).getD [])).flatten =
      ((rangeL K hi).filterMap S.lookup).flatten := by
  rw [flatten_filterMap_getD]
  conv => rhs; rw [flatten_map_filter_dom]
  congr 2
  apply keysSorted_ext (hs.sublist List.filter_sublist)
    ((rangeL_sorted K hi).sublist List.filter_sublist)
  intro x
  simp only [List.mem_filter, mem_rangeL, hdom, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h2, h1⟩
  · rintro ⟨h1, h2⟩; exact ⟨h2, h1⟩

/-- `scan_flatten` over any signed-sorted key list `L` holding exactly the store's keys in
`[K, hi]` (the selected treemap's entries: `Interface/Treemap.lean`'s `sortedEntries`). -/
theorem scan_flatten_sorted {V : Type} (S : GMap w64 (List V)) (L : List w64) (hs : keysSorted L)
    (K hi : w64)
    (hmem : ∀ k, k ∈ L ↔ (sint.Z K ≤ sint.Z k ∧ sint.Z k ≤ sint.Z hi) ∧ (S.lookup k).isSome) :
    (L.map (fun k => (S.lookup k).getD [])).flatten = ((rangeL K hi).filterMap S.lookup).flatten := by
  rw [flatten_filterMap_getD]
  conv => rhs; rw [flatten_map_filter_dom]
  congr 1
  congr 1
  apply keysSorted_ext hs ((rangeL_sorted K hi).sublist List.filter_sublist)
  intro x
  simp only [List.mem_filter, mem_rangeL, hmem]

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
