/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/dist/deployment/boundsOk.lean`. Lean-first.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment.boundsOk

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open Iris Iris.BI Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.etcd.dist

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : deployment.Assumptions]

/-- Go's `m / c` of positive `int`s is the integer quotient. -/
theorem sdiv_pos (m c : w64) (hm : 0 ≤ sint.Z m) (hc : 0 < sint.Z c) :
    sint.Z (BitVec.sdiv m c) = sint.Z m / sint.Z c := by
  have h1 : c ≠ -1#64 := by
    intro h; subst h; revert hc; decide
  have e : sint.Z (BitVec.sdiv m c) = (sint.Z m).tdiv (sint.Z c) :=
    BitVec.toInt_sdiv_of_ne_or_ne _ _ (Or.inr h1)
  rw [e, Int.tdiv_eq_ediv_of_nonneg hm]

/-- The bounds of kinds `0` (kv, `B = 2^60`) and `1`, `2` (watch, cache, `B = 2^62`) as Go checks them. -/
theorem boundsOk_kv (cl op : w64) (B : Int) (hB : B = 2 ^ 60 ∨ B = 2 ^ 62) :
    (0 ≤ sint.Z cl ∧ sint.Z cl < 2 ^ 31 ∧ 0 ≤ sint.Z op ∧ (sint.Z cl = 0 ∨ sint.Z op ≤ (B - 1) / sint.Z cl)) ↔
    (0 ≤ sint.Z cl ∧ sint.Z cl < 2 ^ 31 ∧ 0 ≤ sint.Z op ∧
      (cl = W64 0 ∨ sint.Z op ≤ sint.Z (BitVec.sdiv (W64 (B - 1)) cl))) := by
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, h2, h3, ?_⟩
    rcases h4 with h4 | h4
    · left; word
    · by_cases h0 : cl = W64 0
      · left; exact h0
      · right
        rw [sdiv_pos _ _ (by rcases hB with rfl | rfl <;> word) (by word)]
        have : sint.Z (W64 (B - 1)) = B - 1 := by rcases hB with rfl | rfl <;> word
        rw [this]; exact h4
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, h2, h3, ?_⟩
    rcases h4 with h4 | h4
    · left; subst h4; word
    · by_cases h0 : sint.Z cl = 0
      · left; exact h0
      · right
        rw [sdiv_pos _ _ (by rcases hB with rfl | rfl <;> word) (by omega)] at h4
        have : sint.Z (W64 (B - 1)) = B - 1 := by rcases hB with rfl | rfl <;> word
        rw [this] at h4; exact h4

theorem boundsOk.wp_proof :
    etcd_dist.boundsOk.spec (GF := GF) (hG := hG) := by
  intro w
  obtain ⟨kd, cl, op⟩ := w
  simp only [Workload.val]
  by_cases h0 : kd = W64 0
  · subst h0
    have hiff : Workload.goBoundsOk ⟨W64 0, cl, op⟩ ↔
        (0 ≤ sint.Z cl ∧ sint.Z cl < 2 ^ 31 ∧ 0 ≤ sint.Z op ∧
          (cl = W64 0 ∨ sint.Z op ≤ sint.Z (BitVec.sdiv (W64 (2 ^ 60 - 1)) cl))) := by
      unfold Workload.goBoundsOk; dsimp only; rw [if_pos rfl]
      exact boundsOk_kv cl op (2 ^ 60) (Or.inl rfl)
    rw [show decide (Workload.goBoundsOk ⟨W64 0, cl, op⟩) =
        decide (0 ≤ sint.Z cl ∧ sint.Z cl < 2 ^ 31 ∧ 0 ≤ sint.Z op ∧
          (cl = W64 0 ∨ sint.Z op ≤ sint.Z (BitVec.sdiv (W64 (2 ^ 60 - 1)) cl))) from
        decide_eq_decide.2 hiff]
    generalize hd : decide (0 ≤ sint.Z cl ∧ sint.Z cl < 2 ^ 31 ∧ 0 ≤ sint.Z op ∧
          (cl = W64 0 ∨ sint.Z op ≤ sint.Z (BitVec.sdiv (W64 (2 ^ 60 - 1)) cl))) = d
    clear hiff
    wp_start
    wp_auto
    repeat' wp_if_destruct
    all_goals (try (have hc0 : ¬ sint.Z cl = 0 := by word); try simp only [hc0, ↓reduceIte]; try wp_auto)
    all_goals first
      | (obtain rfl : d = true := by
          rw [← hd]; simp only [decide_eq_true_eq]
          refine ⟨by word, by word, by word, ?_⟩
          first | (left; first | trivial | rfl) | (right; word)
         wp_end)
      | (obtain rfl : d = false := by
          rw [← hd]; simp only [decide_eq_false_iff_not]
          rintro ⟨h1, h2, h3, -⟩; word
         wp_end)
      | (have hne : ¬ cl = W64 0 := ‹_›
         obtain rfl : d = decide (sint.Z op ≤ sint.Z (BitVec.sdiv (W64 1152921504606846975) cl)) := by
          rw [← hd]
          apply decide_eq_decide.2
          constructor
          · rintro ⟨-, -, -, h | h⟩
            · exact absurd h hne
            · exact h
          · intro h; exact ⟨by word, by word, by word, Or.inr h⟩
         wp_end)
  by_cases h1 : kd = W64 1
  · subst h1
    have hiff : Workload.goBoundsOk ⟨W64 1, cl, op⟩ ↔
        (0 ≤ sint.Z cl ∧ sint.Z cl < 2 ^ 31 ∧ 0 ≤ sint.Z op ∧
          (cl = W64 0 ∨ sint.Z op ≤ sint.Z (BitVec.sdiv (W64 (2 ^ 62 - 1)) cl))) := by
      unfold Workload.goBoundsOk; dsimp only; rw [if_neg (by decide), if_pos (Or.inl rfl)]
      exact boundsOk_kv cl op (2 ^ 62) (Or.inr rfl)
    rw [show decide (Workload.goBoundsOk ⟨W64 1, cl, op⟩) =
        decide (0 ≤ sint.Z cl ∧ sint.Z cl < 2 ^ 31 ∧ 0 ≤ sint.Z op ∧
          (cl = W64 0 ∨ sint.Z op ≤ sint.Z (BitVec.sdiv (W64 (2 ^ 62 - 1)) cl))) from
        decide_eq_decide.2 hiff]
    generalize hd : decide (0 ≤ sint.Z cl ∧ sint.Z cl < 2 ^ 31 ∧ 0 ≤ sint.Z op ∧
          (cl = W64 0 ∨ sint.Z op ≤ sint.Z (BitVec.sdiv (W64 (2 ^ 62 - 1)) cl))) = d
    clear hiff
    wp_start
    wp_auto
    repeat' wp_if_destruct
    all_goals (try (have hc0 : ¬ sint.Z cl = 0 := by word); try simp only [hc0, ↓reduceIte]; try wp_auto)
    all_goals first
      | (obtain rfl : d = true := by
          rw [← hd]; simp only [decide_eq_true_eq]
          refine ⟨by word, by word, by word, ?_⟩
          first | (left; first | trivial | rfl) | (right; word)
         wp_end)
      | (obtain rfl : d = false := by
          rw [← hd]; simp only [decide_eq_false_iff_not]
          rintro ⟨h1, h2, h3, -⟩; word
         wp_end)
      | (have hne : ¬ cl = W64 0 := ‹_›
         obtain rfl : d = decide (sint.Z op ≤ sint.Z (BitVec.sdiv (W64 4611686018427387903) cl)) := by
          rw [← hd]
          apply decide_eq_decide.2
          constructor
          · rintro ⟨-, -, -, h | h⟩
            · exact absurd h hne
            · exact h
          · intro h; exact ⟨by word, by word, by word, Or.inr h⟩
         wp_end)
  by_cases h2 : kd = W64 2
  · subst h2
    have hiff : Workload.goBoundsOk ⟨W64 2, cl, op⟩ ↔
        (0 ≤ sint.Z cl ∧ sint.Z cl < 2 ^ 31 ∧ 0 ≤ sint.Z op ∧
          (cl = W64 0 ∨ sint.Z op ≤ sint.Z (BitVec.sdiv (W64 (2 ^ 62 - 1)) cl))) := by
      unfold Workload.goBoundsOk; dsimp only; rw [if_neg (by decide), if_pos (Or.inr rfl)]
      exact boundsOk_kv cl op (2 ^ 62) (Or.inr rfl)
    rw [show decide (Workload.goBoundsOk ⟨W64 2, cl, op⟩) =
        decide (0 ≤ sint.Z cl ∧ sint.Z cl < 2 ^ 31 ∧ 0 ≤ sint.Z op ∧
          (cl = W64 0 ∨ sint.Z op ≤ sint.Z (BitVec.sdiv (W64 (2 ^ 62 - 1)) cl))) from
        decide_eq_decide.2 hiff]
    generalize hd : decide (0 ≤ sint.Z cl ∧ sint.Z cl < 2 ^ 31 ∧ 0 ≤ sint.Z op ∧
          (cl = W64 0 ∨ sint.Z op ≤ sint.Z (BitVec.sdiv (W64 (2 ^ 62 - 1)) cl))) = d
    clear hiff
    wp_start
    wp_auto
    repeat' wp_if_destruct
    all_goals (try (have hc0 : ¬ sint.Z cl = 0 := by word); try simp only [hc0, ↓reduceIte]; try wp_auto)
    all_goals first
      | (obtain rfl : d = true := by
          rw [← hd]; simp only [decide_eq_true_eq]
          refine ⟨by word, by word, by word, ?_⟩
          first | (left; first | trivial | rfl) | (right; word)
         wp_end)
      | (obtain rfl : d = false := by
          rw [← hd]; simp only [decide_eq_false_iff_not]
          rintro ⟨h1, h2, h3, -⟩; word
         wp_end)
      | (have hne : ¬ cl = W64 0 := ‹_›
         obtain rfl : d = decide (sint.Z op ≤ sint.Z (BitVec.sdiv (W64 4611686018427387903) cl)) := by
          rw [← hd]
          apply decide_eq_decide.2
          constructor
          · rintro ⟨-, -, -, h | h⟩
            · exact absurd h hne
            · exact h
          · intro h; exact ⟨by word, by word, by word, Or.inr h⟩
         wp_end)
  by_cases h10 : kd = W64 10
  · subst h10
    have hiff : Workload.goBoundsOk ⟨W64 10, cl, op⟩ ↔ (0 ≤ sint.Z cl ∧ sint.Z cl ≤ 256) := by
      unfold Workload.goBoundsOk; dsimp only
      rw [if_neg (by decide), if_neg (by decide), if_pos rfl]
    rw [show decide (Workload.goBoundsOk ⟨W64 10, cl, op⟩) = decide (0 ≤ sint.Z cl ∧ sint.Z cl ≤ 256) from
        decide_eq_decide.2 hiff]
    generalize hd : decide (0 ≤ sint.Z cl ∧ sint.Z cl ≤ 256) = d
    clear hiff
    wp_start
    wp_auto
    repeat (simp only [decide_false, Bool.not_false, Bool.false_eq_true, ↓reduceIte]; try wp_auto)
    repeat' wp_if_destruct
    all_goals first
      | (obtain rfl : d = true := by
          rw [← hd]; simp only [decide_eq_true_eq]; exact ⟨by word, by word⟩
         wp_end)
      | (obtain rfl : d = false := by
          rw [← hd]; simp only [decide_eq_false_iff_not]; rintro ⟨h1, h2⟩; word
         wp_end)
  rw [show decide (Workload.goBoundsOk ⟨kd, cl, op⟩) = true from decide_eq_true (by
    unfold Workload.goBoundsOk; dsimp only
    rw [if_neg h0, if_neg (by rintro (h | h) <;> contradiction), if_neg h10]; trivial)]
  wp_start
  wp_auto
  repeat (simp only [h0, h1, h2, h10, decide_false, Bool.not_false, Bool.false_eq_true, ↓reduceIte]; try wp_auto)
  wp_end
end proof

end etcd_dist
end EtcdGrove
end Perennial
