/-
The proof of `sort.choosePivot` for any `Less` (`Spec/sort/choosePivotAnyLess.lean`), as Perennial's (`Perennial/Proof/sort/choosePivot.lean`).
-/
module

public import Spec.sort.choosePivotAnyLess
public import Spec.sort.medianAdjacentAnyLess
public import Spec.sort.medianAnyLess
public import Proof.sort.AnyLessBasics

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std
open sortAny

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.sort.Assumptions]

open slices in
theorem sort.choosePivot.wp_proofAnyLess
    (wp_medianAdjacent : EtcdGrove.sort.medianAdjacent.anyLessSpec (GF := GF) (hG := hG))
    (wp_median : EtcdGrove.sort.median.anyLessSpec (GF := GF) (hG := hG)) :
    EtcdGrove.sort.choosePivot.anyLessSpec (GF := GF) (hG := hG) := fun E x R l a b => by
  wp_start as ⟨#Hs, Hl, %Hab_bound⟩
  wp_auto
  have Hl' : sint.Z (b - a) = sint.Z b - sint.Z a := by word
  have Hd := sint_sdiv4 (b - a) (by omega)
  rw [Hl'] at Hd
  generalize BitVec.sdiv (b - a) (W64 4) = d at Hd ⊢
  simp only [W64_1, W64_2, W64_3]
  obtain ⟨Hi, Hj, Hk⟩ := part_choosePivot_idx a b d l.length
    ⟨Hab_bound.1, Hab_bound.2.1, Hab_bound.2.2.1, Hab_bound.2.2.2⟩ Hd
  wp_if_destruct
  · have h8 : 8 ≤ sint.Z b - sint.Z a := by rw [← Hl']; exact Hif
    wp_if_destruct
    · wp_apply wp_medianAdjacent E x R l (a + d * 1) swaps_ptr _ $$ [Hl swaps]
        with %ri %sw1 ⟨Hl, swaps, %Hri⟩
      · iframe; iframe #; ipureintro; rw [Hi]; omega
      wp_apply wp_medianAdjacent E x R l (a + d * 2) swaps_ptr _ $$ [Hl swaps]
        with %rj %sw2 ⟨Hl, swaps, %Hrj⟩
      · iframe; iframe #; ipureintro; rw [Hj]; omega
      wp_apply wp_medianAdjacent E x R l (a + d * 3) swaps_ptr _ $$ [Hl swaps]
        with %rk %sw3 ⟨Hl, swaps, %Hrk⟩
      · iframe; iframe #; ipureintro; rw [Hk]; omega
      rw [Hi] at Hri; rw [Hj] at Hrj; rw [Hk] at Hrk
      wp_apply wp_median E x R l ri rj rk swaps_ptr _ $$ [Hl swaps]
        with %r %sw4 ⟨Hl, swaps, %Hr⟩
      · iframe; iframe #; ipureintro; omega
      have : sint.Z a ≤ sint.Z r ∧ sint.Z r < sint.Z b := by
        rcases Hr with h | h | h <;> subst h <;> omega
      wp_if_destruct <;> (try wp_if_destruct) <;> ((try simp only [_root_.Perennial.sort.increasingHint, _root_.Perennial.sort.decreasingHint, _root_.Perennial.sort.unknownHint]); wp_auto; iapply HΦ; iframe; ipureintro; exact this)
    · wp_apply wp_median E x R l (a + d * 1) (a + d * 2) (a + d * 3) swaps_ptr _ $$ [Hl swaps]
        with %r %sw4 ⟨Hl, swaps, %Hr⟩
      · iframe; iframe #; ipureintro; rw [Hi, Hj, Hk]; omega
      have : sint.Z a ≤ sint.Z r ∧ sint.Z r < sint.Z b := by
        rcases Hr with h | h | h <;> subst h <;> omega
      wp_if_destruct <;> (try wp_if_destruct) <;> ((try simp only [_root_.Perennial.sort.increasingHint, _root_.Perennial.sort.decreasingHint, _root_.Perennial.sort.unknownHint]); wp_auto; iapply HΦ; iframe; ipureintro; exact this)
  · have : sint.Z a ≤ sint.Z (a + d * 2) ∧ sint.Z (a + d * 2) < sint.Z b := by
      rw [Hj]; omega
    (try wp_if_destruct) <;> (try wp_if_destruct) <;> ((try simp only [_root_.Perennial.sort.increasingHint, _root_.Perennial.sort.decreasingHint, _root_.Perennial.sort.unknownHint]); wp_auto; iapply HΦ; iframe; ipureintro; exact this)

end proof

end EtcdGrove
end Perennial
