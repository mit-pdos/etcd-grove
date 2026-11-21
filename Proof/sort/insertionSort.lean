/-
The proof of `sort.insertionSort` (`Spec/sort/insertionSort.lean`): its loops compute
`stableModel.insOuter` and `stableModel.insInner` (the loop structure of Perennial's proof of
the same function, `Perennial/Proof/sort/insertionSort.lean`).
-/
module

public import Spec.sort.insertionSort

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std
open stableModel

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.sort.Assumptions]

theorem sort.insertionSort.wp_proof : EtcdGrove.sort.insertionSort.spec (GF := GF) (hG := hG) :=
    fun E x R lt l a b => by
  wp_start as ⟨#Hs, Hl, %Hb⟩
  ihave #Hsrt := sorterSpec_isSorter x R lt $$ Hs
  wp_auto
  ihave HI1 : (∃ (i : w64) (L : List E),
      "i" ∷ i_ptr ↦ i ∗
      "Hl" ∷ R L ∗
      "%Hi" ∷ ⌜sint.Z a + 1 ≤ sint.Z i ∧ sint.Z i ≤ max (sint.Z a + 1) (sint.Z b) ∧
        L.length = l.length ∧
        insOuter lt (sint.nat a) (sint.nat b) (sint.nat i) L =
          insertionSortM lt l (sint.nat a) (sint.nat b)⌝ : IProp GF) $$ [i Hl]
  · iexists (a + W64 1), l
    iframe
    ipureintro
    refine ⟨by word, by word, rfl, ?_⟩
    unfold insertionSortM
    rw [show sint.nat (a + W64 1) = sint.nat a + 1 by word]
  wp_for HI1
  obtain ⟨Hi1, Hi2, HL, Heq⟩ := Hi
  by_cases Hif : sint.Z i < sint.Z b
  · simp only [Hif, _root_.decide_true, ↓reduceIte]
    wp_auto
    ihave HI2 : (∃ (j : w64) (L' : List E),
        "j" ∷ j_ptr ↦ j ∗
        "Hl" ∷ R L' ∗
        "%Hj" ∷ ⌜sint.Z a ≤ sint.Z j ∧ sint.Z j ≤ sint.Z i ∧ L'.length = l.length ∧
          insOuter lt (sint.nat a) (sint.nat b) (sint.nat i + 1)
            (insInner lt (sint.nat a) (sint.nat j) L') =
          insertionSortM lt l (sint.nat a) (sint.nat b)⌝ : IProp GF) $$ [j Hl]
    · iexists i, L
      iframe
      ipureintro
      refine ⟨by word, by word, HL, ?_⟩
      rw [← Heq]
      conv => rhs; unfold insOuter
      rw [dif_pos (by word)]
    wp_for HI2
    obtain ⟨Hj1, Hj2, HL', Heq'⟩ := Hj
    wp_if_destruct
    · list_elem L' (sint.nat j) as x0
      list_elem L' (sint.nat (j - W64 1)) as x1
      wp_apply _root_.Perennial.sort.wp_sorter_Less x R (fun a b => lt a b = true) L' j
        (j - W64 1) x0 x1 (by word) (by word) Hx0_lookup Hx1_lookup $$ [$Hsrt $Hl]
        as %r ⟨Hl, %Hr⟩
      have hj1 : sint.nat (j - W64 1) = sint.nat j - 1 := by word
      rw [hj1] at Hx1_lookup
      have hless : lessL lt L' (sint.nat j) (sint.nat j - 1) = lt x0 x1 :=
        lessL_eq lt L' _ _ x0 x1 Hx0_lookup Hx1_lookup
      cases r
      · bool_if
        have hlt : lt x0 x1 = false := by
          cases h : lt x0 x1
          · rfl
          · exact absurd (Hr.2 h) (by simp)
        wp_for_post
        iframe
        iexists (i + W64 1), L'
        iframe
        ipureintro
        refine ⟨by word, by word, HL', ?_⟩
        rw [← Heq', show sint.nat (i + W64 1) = sint.nat i + 1 by word]
        congr 1
        unfold insInner
        rw [dif_neg (by rw [hless, hlt]; simp)]
      · bool_if
        wp_auto
        wp_apply _root_.Perennial.sort.wp_sorter_Swap x R (fun a b => lt a b = true) L' j
          (j - W64 1) x0 x1 (by word) (by word) Hx0_lookup (by rw [hj1]; exact Hx1_lookup)
          $$ [$Hsrt $Hl] as Hl
        have hlt : lt x0 x1 = true := Hr.1 rfl
        wp_for_post
        iframe
        iexists (j - W64 1), _
        iframe
        ipureintro
        refine ⟨by word, by word, ?_, ?_⟩
        · simp
          exact HL'
        · rw [← Heq', hj1]
          congr 1
          conv => rhs; unfold insInner
          rw [dif_pos ⟨by word, by rw [hless, hlt]⟩]
          congr 1
          rw [swapL_eq _ _ _ _ _ Hx0_lookup Hx1_lookup]
          first
            | exact _root_.Perennial.sort.swap_set_comm L' (sint.nat j) (sint.nat j - 1) x0 x1
                Hx0_lookup Hx1_lookup
            | exact (_root_.Perennial.sort.swap_set_comm L' (sint.nat j) (sint.nat j - 1) x0 x1
                Hx0_lookup Hx1_lookup).symm
    · wp_for_post
      iframe
      iexists (i + W64 1), L'
      iframe
      ipureintro
      refine ⟨by word, by word, HL', ?_⟩
      rw [← Heq', show sint.nat (i + W64 1) = sint.nat i + 1 by word]
      congr 1
      unfold insInner
      rw [dif_neg (by word)]
  · simp only [Hif, decide_false, Bool.false_eq_true, ↓reduceIte]
    wp_auto
    iapply HΦ
    rw [← Heq]
    unfold insOuter
    rw [dif_neg (by word)]
    iexact Hl
