/-
The proof of `sort.insertionSort` for any `Less` (`Spec/sort/insertionSortAnyLess.lean`): the loops of Perennial's proof (`Perennial/Proof/sort/insertionSort.lean`), without the order.
-/
module

public import Spec.sort.insertionSortAnyLess
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

theorem sort.insertionSort.wp_proofAnyLess :
    EtcdGrove.sort.insertionSort.anyLessSpec (GF := GF) (hG := hG) := fun E x R l a b => by
  wp_start as ⟨#Hs, Hl, %Hb⟩
  wp_auto
  ihave HI1 : (∃ (i : w64) (L : List E),
      "i" ∷ i_ptr ↦ i ∗
      "Hl" ∷ R L ∗
      "%Hi" ∷ ⌜sint.Z a + 1 ≤ sint.Z i ∧ sint.Z i ≤ max (sint.Z a + 1) (sint.Z b) ∧
        l.Perm L⌝ : IProp GF) $$ [i Hl]
  · iexists (a + W64 1), l
    iframe
    ipureintro
    exact ⟨by word, by word, List.Perm.refl _⟩
  wp_for HI1
  obtain ⟨Hi1, Hi2, HP⟩ := Hi
  by_cases Hif : sint.Z i < sint.Z b
  · simp only [Hif, _root_.decide_true, ↓reduceIte]
    wp_auto
    ihave HI2 : (∃ (j : w64) (L' : List E),
        "j" ∷ j_ptr ↦ j ∗
        "Hl" ∷ R L' ∗
        "%Hj" ∷ ⌜sint.Z a ≤ sint.Z j ∧ sint.Z j ≤ sint.Z i ∧ l.Perm L'⌝ : IProp GF) $$ [j Hl]
    · iexists i, L
      iframe
      ipureintro
      exact ⟨by word, by word, HP⟩
    wp_for HI2
    obtain ⟨Hj1, Hj2, HP'⟩ := Hj
    have HL' := HP'.length_eq
    wp_if_destruct
    · list_elem L' (sint.nat j) as x0
      list_elem L' (sint.nat (j - W64 1)) as x1
      wp_apply wp_any_Less x R L' j (j - W64 1) x0 x1 (by word) (by word)
        Hx0_lookup Hx1_lookup $$ [$Hs $Hl] as %r Hl
      cases r
      · bool_if
        wp_for_post
        iframe
        iexists (i + W64 1), L'
        iframe
        ipureintro
        exact ⟨by word, by word, HP'⟩
      · bool_if
        wp_auto
        wp_apply wp_any_Swap x R L' j (j - W64 1) x0 x1 (by word) (by word)
          Hx0_lookup Hx1_lookup $$ [$Hs $Hl] as %L2 ⟨Hl, %Hp2⟩
        wp_for_post
        iframe
        iexists (j - W64 1), L2
        iframe
        ipureintro
        exact ⟨by word, by word, HP'.trans Hp2⟩
    · wp_for_post
      iframe
      iexists (i + W64 1), L'
      iframe
      ipureintro
      exact ⟨by word, by word, HP'⟩
  · simp only [Hif, decide_false, Bool.false_eq_true, ↓reduceIte]
    wp_auto
    iapply HΦ
    iframe
    ipureintro
    exact HP

end proof

end EtcdGrove
end Perennial
