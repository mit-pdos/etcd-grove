/-
**Sorting by a key with distinct values** (structured-merge-diff v7.0.0): Go's string `<` is
`gsLt`, and a permutation sorted by a strict order on distinct keys is `mergeSort`'s result (so
whatever order `sort.SliceStable` leaves, `FieldList.Sort` ends at `mergeSort`; the lexical map
zip's sorted key list is `zipKeys`). A defs-tier module. Prove phase (2026-11-20, B2c).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.LawProofsPure

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open sigs_k8s_io.structured_merge_diff.v7

namespace ValuePure

/-- Go's string `<` is `gsLt`. -/
theorem goStringLt_iff_gsLt (a b : GoString) : go.GoStringLt a b ↔ gsLt a b = true := by
  rw [gsLt_iff, ← compareResult_gs]
  unfold strings.compareResult
  by_cases h : go.GoStringLt a b
  · simp only [h, ↓reduceIte, true_iff]; decide
  · simp only [h, ↓reduceIte, false_iff]
    split <;> decide

theorem gsLt_iff_goStringLt (a b : GoString) : gsLt a b = true ↔ go.GoStringLt a b :=
  (goStringLt_iff_gsLt a b).symm

theorem gsLt_false_cases {a b : GoString} (h : gsLt a b = false) : gsLt b a = true ∨ a = b := by
  cases h' : gsLt b a
  · exact Or.inr (gsLt_total h h')
  · exact Or.inl rfl

/-- `¬ b < a` is transitive. -/
theorem gsLt_false_trans {a b c : GoString} (h1 : gsLt b a = false) (h2 : gsLt c b = false) :
    gsLt c a = false := by
  cases h : gsLt c a
  · rfl
  · exfalso
    rcases gsLt_false_cases h2 with h3 | rfl
    · rw [gsLt_trans h3 h] at h1; cases h1
    · rw [h] at h1; cases h1

theorem nodup_map_inj {α β : Type} {f : α → β} : ∀ {l : List α}, (l.map f).Nodup →
    ∀ {a b}, a ∈ l → b ∈ l → f a = f b → a = b
  | [], _, _, _, ha, _, _ => by simp at ha
  | x :: l, h, a, b, ha, hb, e => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at h
    simp only [List.mem_cons] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · rfl
    · exact absurd ⟨b, hb, e.symm⟩ h.1
    · exact absurd ⟨a, ha, e⟩ h.1
    · exact nodup_map_inj h.2 ha hb e

/-- A permutation, sorted (`¬ key b < key a` for each earlier `a`), of a list with distinct
keys is `mergeSort`'s result. -/
theorem eq_mergeSort_of_perm_sorted {α : Type} (key : α → GoString) (xs ys : List α)
    (hnd : (xs.map key).Nodup) (hp : ys.Perm xs)
    (hs : ys.Pairwise (fun a b => gsLt (key b) (key a) = false)) :
    ys = xs.mergeSort (fun a b => !gsLt (key b) (key a)) := by
  have hm := List.mergeSort_perm xs (fun a b => !gsLt (key b) (key a))
  have hsm : (xs.mergeSort (fun a b => !gsLt (key b) (key a))).Pairwise
      (fun a b => gsLt (key b) (key a) = false) := by
    have := List.pairwise_mergeSort (le := fun a b => !gsLt (key b) (key a))
      (fun a b c h1 h2 => by
        simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at h1 h2 ⊢
        exact gsLt_false_trans h1 h2)
      (fun a b => by
        cases h1 : gsLt (key b) (key a) <;> cases h2 : gsLt (key a) (key b) <;> simp
        have := gsLt_trans h1 h2; rw [gsLt_irrefl] at this; cases this) xs
    simpa using this
  have hnd' : (ys.map key).Nodup := (hp.map key).nodup_iff.2 hnd
  apply List.Perm.eq_of_pairwise _ hs hsm (hp.trans hm.symm)
  intro a b ha hb h1 h2
  have hb' : b ∈ ys := (hp.trans hm.symm).symm.subset hb
  have hk : key a = key b := gsLt_total h2 h1
  exact nodup_map_inj hnd' ha hb' hk

/-- The lexical zip's keys, collected: the left map's keys (any order), then the right map's not
on the left (any order), are a permutation of `zipKeys`. -/
theorem zipKeys_perm_collect (ol or_ : Option (List (GoString × UVal)))
    (hl : keysSorted (kvsOrEmpty ol) = true) (hr : keysSorted (kvsOrEmpty or_) = true)
    (d1 d2 : List GoString) (h1 : d1.Perm (kvKeys (kvsOrEmpty ol)))
    (h2 : d2.Perm (kvKeys (kvsOrEmpty or_))) :
    (d1 ++ d2.filter (fun k => !(lookupKV k (kvsOrEmpty ol)).isSome)).Perm (zipKeys ol or_) := by
  have hn1 : d1.Nodup := h1.nodup_iff.2 (keysSorted_nodup _ hl)
  have hn2 : d2.Nodup := h2.nodup_iff.2 (keysSorted_nodup _ hr)
  apply perm_of_nodup_mem
  · rw [List.nodup_append]
    refine ⟨hn1, hn2.filter _, ?_⟩
    intro a ha b hb hab
    subst hab
    have ha' := (lookupKV_isSome_iff a _).2 (h1.mem_iff.1 ha)
    simp at hb
    rw [hb.2] at ha'; cases ha'
  · apply zipKeys_nodup_law_holds
    · intro kvs h; subst h; exact hl
    · intro kvs h; subst h; exact hr
  · intro a
    rw [zipKeys_mem_law_holds, List.mem_append, List.mem_filter, h1.mem_iff, h2.mem_iff,
      ← lookupKV_isSome_iff, ← lookupKV_isSome_iff]
    by_cases h : (lookupKV a (kvsOrEmpty ol)).isSome <;> simp [h]

/-- `sort.Strings`' result on a permutation of `zipKeys` is `zipKeys`. -/
theorem eq_zipKeys_of_perm_sorted (ol or_ : Option (List (GoString × UVal)))
    (hl : keysSorted (kvsOrEmpty ol) = true) (hr : keysSorted (kvsOrEmpty or_) = true)
    (ys : List GoString) (hp : ys.Perm (zipKeys ol or_))
    (hs : ∀ (i j : Nat) (xi xj : GoString), ys[i]? = some xi → ys[j]? = some xj → i < j →
      go.GoStringLe xi xj) :
    ys = zipKeys ol or_ := by
  have hz : (zipKeys ol or_).Pairwise go.GoStringLe := by
    have := zipLexical_sorted ((kvsOrEmpty ol).length + (kvsOrEmpty or_).length + 1)
      (kvsOrEmpty ol) (kvsOrEmpty or_) (by omega) hl hr
    unfold zipKeys
    refine this.imp ?_
    intro a b h
    exact Or.inr ((goStringLt_iff_gsLt a b).2 h)
  have hy : ys.Pairwise go.GoStringLe := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    exact hs i j _ _ (List.getElem?_eq_getElem hi) (List.getElem?_eq_getElem hj) hij
  apply List.Perm.eq_of_pairwise _ hy hz hp
  intro a b _ _ h1 h2
  rcases h1 with h1 | h1
  · exact h1
  rcases h2 with h2 | h2
  · exact h2.symm
  exact absurd h2 (go.goStringLt_asymm h1)

theorem zipKeys_length_le (ol or_ : Option (List (GoString × UVal)))
    (hl : keysSorted (kvsOrEmpty ol) = true) (hr : keysSorted (kvsOrEmpty or_) = true) :
    (zipKeys ol or_).length ≤ (kvsOrEmpty ol).length + (kvsOrEmpty or_).length := by
  have hn : (zipKeys ol or_).Nodup := by
    apply zipKeys_nodup_law_holds
    · intro kvs h; subst h; exact hl
    · intro kvs h; subst h; exact hr
  have hsub : zipKeys ol or_ ⊆ kvKeys (kvsOrEmpty ol) ++ kvKeys (kvsOrEmpty or_) := by
    intro k hk
    rw [zipKeys_mem_law_holds] at hk
    rw [List.mem_append]
    rcases hk with h | h
    · exact Or.inl ((lookupKV_isSome_iff k _).1 h)
    · exact Or.inr ((lookupKV_isSome_iff k _).1 h)
  have := List.Nodup.length_le_of_subset hn hsub
  simpa [kvKeys] using this

theorem take_append_getElem_prefix {α : Type} (l : List α) (i : Nat) (h : i < l.length) :
    (l.take i ++ [l[i]]).IsPrefix l := by
  rw [List.take_append_getElem h]
  exact List.take_prefix _ _

end ValuePure

end smd
end EtcdGrove
end Perennial
