/-
**`PathElementSet.Intersection`'s and `PathElementSet.Difference`'s merge steps**: what the
output holds after each step of the two-pointer loop over sorted lists (`fpA.Front`).

Prove phase (2026-11-20, notes/smd-plan.md).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofsPESet
import all Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Defs
import all Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Vocab

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open sigs_k8s_io.structured_merge_diff.v7

namespace fpA

variable {xs ys : List PE} {i j : Nat}

theorem consumed_x (hf : Front xs ys i j) (hwx : AllWf xs) (hwy : AllWf ys) {a : PE}
    (ha : a ∈ xs.take i ∨ a ∈ ys.take j) (hb : a ∈ xs.drop i ∨ a ∈ ys.drop j) : False :=
  front_not_left hf hwx hwy a (List.mem_append.2 ha) (List.mem_append.2 hb)

/-! ## Intersection: `x ∈ out ↔ x ∈ xs.take i ∧ x ∈ ys.take j` -/

theorem inter_mem_x (hf : Front xs ys i j) (hwx : AllWf xs) (hwy : AllWf ys)
    (hi : i < xs.length) (x : PE) :
    (x ∈ xs.take (i + 1) ∧ x ∈ ys.take j) ↔ (x ∈ xs.take i ∧ x ∈ ys.take j) := by
  rw [take_succ' xs i hi, List.mem_append, List.mem_singleton]
  constructor
  · rintro ⟨h | rfl, h2⟩
    · exact ⟨h, h2⟩
    · exact (consumed_x hf hwx hwy (Or.inr h2) (Or.inl (getElem_mem_drop xs i hi))).elim
  · rintro ⟨h, h2⟩; exact ⟨Or.inl h, h2⟩

theorem inter_mem_y (hf : Front xs ys i j) (hwx : AllWf xs) (hwy : AllWf ys)
    (hj : j < ys.length) (x : PE) :
    (x ∈ xs.take i ∧ x ∈ ys.take (j + 1)) ↔ (x ∈ xs.take i ∧ x ∈ ys.take j) := by
  rw [take_succ' ys j hj, List.mem_append, List.mem_singleton]
  constructor
  · rintro ⟨h, h2 | rfl⟩
    · exact ⟨h, h2⟩
    · exact (consumed_x hf hwx hwy (Or.inl h) (Or.inr (getElem_mem_drop ys j hj))).elim
  · rintro ⟨h, h2⟩; exact ⟨h, Or.inl h2⟩

theorem inter_mem_eq (hf : Front xs ys i j) (hwx : AllWf xs) (hwy : AllWf ys)
    (hi : i < xs.length) (hj : j < ys.length) (he : xs[i] = ys[j]) (x : PE) :
    (x ∈ xs.take (i + 1) ∧ x ∈ ys.take (j + 1)) ↔ ((x ∈ xs.take i ∧ x ∈ ys.take j) ∨ x = xs[i]) := by
  rw [take_succ' xs i hi, take_succ' ys j hj, List.mem_append, List.mem_append,
    List.mem_singleton, List.mem_singleton]
  constructor
  · rintro ⟨h | rfl, h2 | h2⟩
    · exact Or.inl ⟨h, h2⟩
    · subst h2
      exact (consumed_x hf hwx hwy (Or.inl h) (Or.inr (getElem_mem_drop ys j hj))).elim
    · exact (consumed_x hf hwx hwy (Or.inr h2) (Or.inl (getElem_mem_drop xs i hi))).elim
    · exact Or.inr rfl
  · rintro (⟨h, h2⟩ | rfl)
    · exact ⟨Or.inl h, Or.inl h2⟩
    · exact ⟨Or.inr rfl, Or.inr he⟩

theorem inter_mem_final (hf : Front xs ys i j) (hwx : AllWf xs) (hwy : AllWf ys)
    (hend : xs.drop i = [] ∨ ys.drop j = []) (x : PE) :
    (x ∈ xs.take i ∧ x ∈ ys.take j) ↔ (x ∈ xs ∧ x ∈ ys) := by
  rw [mem_take_drop xs i x, mem_take_drop ys j x]
  constructor
  · rintro ⟨h, h2⟩; exact ⟨Or.inl h, Or.inl h2⟩
  · rintro ⟨h | h, h2 | h2⟩
    · exact ⟨h, h2⟩
    · exact (consumed_x hf hwx hwy (Or.inl h) (Or.inr h2)).elim
    · exact (consumed_x hf hwx hwy (Or.inr h2) (Or.inl h)).elim
    · rcases hend with e | e
      · rw [e] at h; simp at h
      · rw [e] at h2; simp at h2

/-! ## Difference: `x ∈ out ↔ x ∈ xs.take i ∧ x ∉ ys` -/

theorem diff_mem_x (hf : Front xs ys i j) (hwx : AllWf xs) (hwy : AllWf ys) (hsy : PE.Sorted ys)
    (hi : i < xs.length) (hj : j < ys.length) (hlt : PE.lt xs[i] ys[j]) (x : PE) :
    (x ∈ xs.take (i + 1) ∧ x ∉ ys) ↔ ((x ∈ xs.take i ∧ x ∉ ys) ∨ x = xs[i]) := by
  have hw : xs[i].wf = true := hwx _ (List.getElem_mem hi)
  have hnot : xs[i] ∉ ys := by
    intro hm
    rcases (mem_take_drop ys j _).1 hm with h | h
    · exact consumed_x hf hwx hwy (Or.inr h) (Or.inl (getElem_mem_drop xs i hi))
    · exact lt_irrefl _ hw (lt_rest hwy hsy j hj _ hw hlt _ h)
  rw [take_succ' xs i hi, List.mem_append, List.mem_singleton]
  constructor
  · rintro ⟨h | rfl, h2⟩
    · exact Or.inl ⟨h, h2⟩
    · exact Or.inr rfl
  · rintro (⟨h, h2⟩ | rfl)
    · exact ⟨Or.inl h, h2⟩
    · exact ⟨Or.inr rfl, hnot⟩

theorem diff_mem_eq (hi : i < xs.length) (hj : j < ys.length) (he : xs[i] = ys[j]) (x : PE) :
    (x ∈ xs.take (i + 1) ∧ x ∉ ys) ↔ (x ∈ xs.take i ∧ x ∉ ys) := by
  rw [take_succ' xs i hi, List.mem_append, List.mem_singleton]
  constructor
  · rintro ⟨h | rfl, h2⟩
    · exact ⟨h, h2⟩
    · exact absurd (he ▸ List.getElem_mem hj) h2
  · rintro ⟨h, h2⟩; exact ⟨Or.inl h, h2⟩

/-- `ys` consumed: the rest of `xs` is not in `ys`. -/
theorem diff_mem_tail (hf : Front xs ys i ys.length) (hwx : AllWf xs) (hwy : AllWf ys) (x : PE) :
    (x ∈ xs ∧ x ∉ ys) ↔ ((x ∈ xs.take i ∧ x ∉ ys) ∨ x ∈ xs.drop i) := by
  rw [mem_take_drop xs i x]
  constructor
  · rintro ⟨h | h, h2⟩
    · exact Or.inl ⟨h, h2⟩
    · exact Or.inr h
  · rintro (⟨h, h2⟩ | h)
    · exact ⟨Or.inl h, h2⟩
    · refine ⟨Or.inr h, fun h2 => ?_⟩
      have : x ∈ ys.take ys.length := by rw [List.take_length]; exact h2
      exact consumed_x hf hwx hwy (Or.inr this) (Or.inl h)

theorem diff_mem_final (hi : xs.drop i = []) (x : PE) :
    (x ∈ xs.take i ∧ x ∉ ys) ↔ (x ∈ xs ∧ x ∉ ys) := by
  rw [mem_take_drop xs i x, hi]
  simp

end fpA

end smd
end EtcdGrove
end Perennial
