/-
The proof of `sort.heapSort` for any `Less` (`Spec/sort/heapSortAnyLess.lean`): the loops of Perennial's proof (`Perennial/Proof/sort/heapSort.lean`), without the heap.
-/
module

public import Spec.sort.heapSortAnyLess
public import Spec.sort.siftDownAnyLess
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
theorem sort.heapSort.wp_proofAnyLess
    (wp_siftDown : EtcdGrove.sort.siftDown.anyLessSpec (GF := GF) (hG := hG)) :
    EtcdGrove.sort.heapSort.anyLessSpec (GF := GF) (hG := hG) := fun E x R l a b => by
  wp_start as ⟨#Hs, Hl, %Hab⟩
  wp_auto
  have hn : sint.Z (b - a) = sint.Z b - sint.Z a := by word
  have hi0 : sint.Z (BitVec.sdiv (b - a - W64 1) (W64 2)) = (sint.Z b - sint.Z a - 1) / 2 := by
    rw [sdiv2_nonneg _ (by word)]; word
  -- the heapify loop
  ihave HI1 : (∃ (i_val : w64) (L : List E),
      "i" ∷ i_ptr ↦ i_val ∗
      "Hl" ∷ R L ∗
      "%Hir" ∷ ⌜-1 ≤ sint.Z i_val ∧ sint.Z i_val ≤ sint.Z b - sint.Z a - 1 ∧ l.Perm L⌝ : IProp GF)
      $$ [i Hl]
  · iexists _, l
    iframe
    ipureintro
    exact ⟨by omega, by omega, List.Perm.refl _⟩
  wp_for HI1
  obtain ⟨Hi1, Hi2, HP1⟩ := Hir
  have hl1 := HP1.length_eq
  wp_if_destruct
  · wp_apply wp_siftDown E x R L i_val (b - a) a $$ [Hl] with %L' ⟨Hl, %HP'⟩
    · iframe Hl; iframe #; ipureintro
      refine ⟨by word, by word, by word, by word, by word, by word⟩
    wp_for_post
    iframe
    iexists (i_val - W64 1), L'
    iframe
    ipureintro
    exact ⟨by word, by word, HP1.trans HP'⟩
  · -- the sorting loop
    ihave HI2 : (∃ (i_val : w64) (L : List E),
        "i" ∷ i_ptr ↦ i_val ∗
        "Hl" ∷ R L ∗
        "%Hir" ∷ ⌜-1 ≤ sint.Z i_val ∧ sint.Z i_val ≤ sint.Z b - sint.Z a - 1 ∧ l.Perm L⌝ :
          IProp GF) $$ [i Hl]
    · iexists _, L
      iframe
      ipureintro
      exact ⟨by word, by word, HP1⟩
    wp_for HI2
    obtain ⟨Hj1, Hj2, HP2⟩ := Hir
    have hl2 := HP2.length_eq
    wp_if_destruct
    · list_elem L (sint.nat a) as x0
      list_elem L (sint.nat (a + i_val)) as xi
      wp_apply wp_any_Swap x R L a (a + i_val) x0 xi (by word) (by word) Hx0_lookup Hxi_lookup
        $$ [$Hs $Hl] as %L2 ⟨Hl, %HP3⟩
      have hl3 := HP3.length_eq
      wp_apply wp_siftDown E x R L2 (W64 0) i_val a $$ [Hl] with %L3 ⟨Hl, %HP4⟩
      · iframe Hl; iframe #; ipureintro
        refine ⟨by word, by word, by word, by word, by word, by word⟩
      wp_for_post
      iframe
      iexists (i_val - W64 1), L3
      iframe
      ipureintro
      exact ⟨by word, by word, (HP2.trans HP3).trans HP4⟩
    · iapply HΦ
      iframe
      ipureintro
      exact HP2

end proof

end EtcdGrove
end Perennial
