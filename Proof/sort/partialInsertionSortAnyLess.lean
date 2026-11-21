/-
The proof of `sort.partialInsertionSort` for any `Less` (`Spec/sort/partialInsertionSortAnyLess.lean`): the loops of Perennial's proof (`Perennial/Proof/sort/partialInsertionSort.lean`), without the order. Perennial's proof shows from the segment's header that the left shift stops at `a`; for any `Less` it may go below `a`, down to index 0 (`j >= 1`), still in the list.
-/
module

public import Spec.sort.partialInsertionSortAnyLess
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

theorem sort.partialInsertionSort.wp_proofAnyLess :
    EtcdGrove.sort.partialInsertionSort.anyLessSpec (GF := GF) (hG := hG) :=
    fun E x R l a b => by
  wp_start as ⟨#Hs, Hl, %Hab_bound⟩
  wp_auto
  ihave HI : (∃ (jc i_val : w64) (L : List E),
      "jc" ∷ j_ptr ↦ jc ∗
      "i" ∷ i_ptr ↦ i_val ∗
      "Hl" ∷ R L ∗
      "%irange" ∷ ⌜sint.Z a + 1 ≤ sint.Z i_val ∧ sint.Z i_val ≤ sint.Z b ∧ l.Perm L⌝ : IProp GF)
      $$ [j i Hl]
  · iexists _, _, l
    iframe
    ipureintro
    exact ⟨by word, by word, List.Perm.refl _⟩
  wp_for HI
  by_cases Hjc : sint.Z jc < sint.Z (W64 5)
  case neg =>
    simp only [Hjc, decide_false, Bool.false_eq_true, ↓reduceIte]
    wp_auto
    iapply HΦ
    iframe
    ipureintro
    exact irange.2.2
  simp only [Hjc, _root_.decide_true, ↓reduceIte]
  wp_auto
  ihave HS : (∃ (i_val : w64) (L : List E),
      "i" ∷ i_ptr ↦ i_val ∗
      "Hl" ∷ R L ∗
      "%irange" ∷ ⌜sint.Z a + 1 ≤ sint.Z i_val ∧ sint.Z i_val ≤ sint.Z b ∧ l.Perm L⌝ : IProp GF)
      $$ [i Hl]
  · iexists _, _
    iframe
    ipureintro
    exact irange
  clear irange i_val L
  wp_for HS
  obtain ⟨Hi1, Hi2, HP1⟩ := irange
  have hlen' := HP1.length_eq
  wp_if_destruct
  · list_elem L (sint.nat i_val) as x0
    list_elem L (sint.nat (i_val - W64 1)) as x1
    wp_apply wp_any_Less x R L i_val (i_val - W64 1) x0 x1 (by word) (by word)
      Hx0_lookup Hx1_lookup $$ [$Hs $Hl] as %r Hl
    cases r
    case false =>
      -- keep scanning
      simp only [Bool.not_false]
      (try bool_if)
      wp_auto
      wp_for_post
      iframe
      iexists (i_val + W64 1), L
      iframe
      ipureintro
      exact ⟨by word, by word, HP1⟩
    simp only [Bool.not_true]
    (try bool_if)
    wp_auto
    wp_if_destruct
    · subst Hif; omega
    wp_if_destruct
    · -- short slice: give up
      wp_for_post
      iapply HΦ
      iframe
      ipureintro
      exact HP1
    -- swap `data[i]` and `data[i-1]`
    wp_apply wp_any_Swap x R L i_val (i_val - W64 1) x0 x1 (by word) (by word)
      Hx0_lookup Hx1_lookup $$ [$Hs $Hl] as %L2 ⟨Hl, %HP2⟩
    have Hperm2 := HP1.trans HP2
    have hlen2 := Hperm2.length_eq
    clear Hx0_lookup Hx1_lookup x0 x1 HP1 HP2 hlen'
    -- join point after shifting the smaller element to the left
    wp_bind (If _ _ _)
    iapply wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ ∃ L3,
        "Hl" ∷ R L3 ∗ "i" ∷ i_ptr ↦ i_val ∗ "a" ∷ a_ptr ↦ a ∗
        "data" ∷ data_ptr ↦ (interface.ok x : GoInterface) ∗
        "%Hperm3" ∷ ⌜l.Perm L3⌝)) $$ [Hl i a data]
    · wp_if_destruct
      · ihave HL : (∃ (jl : w64) (L3 : List E),
            "jl" ∷ j_ptr ↦ jl ∗
            "Hl" ∷ R L3 ∗
            "%jrange" ∷ ⌜0 ≤ sint.Z jl ∧ sint.Z jl ≤ sint.Z i_val - 1 ∧ l.Perm L3⌝ : IProp GF)
            $$ [j Hl]
        · iexists _, L2
          iframe
          ipureintro
          exact ⟨by word, by word, Hperm2⟩
        wp_for HL
        obtain ⟨Hj1, Hj2, Hperm3⟩ := jrange
        have hlen3 := Hperm3.length_eq
        by_cases Hjl : sint.Z (W64 1) ≤ sint.Z jl
        case neg =>
          simp only [Hjl, decide_false, Bool.false_eq_true, ↓reduceIte]
          isplitl []
          · itrivial
          iexists L3
          iframe
          ipureintro
          exact Hperm3
        simp only [Hjl, _root_.decide_true, ↓reduceIte]
        wp_auto
        list_elem L3 (sint.nat jl) as y0
        list_elem L3 (sint.nat (jl - W64 1)) as y1
        wp_apply wp_any_Less x R L3 jl (jl - W64 1) y0 y1 (by word) (by word)
          Hy0_lookup Hy1_lookup $$ [$Hs $Hl] as %r' Hl
        cases r'
        case false =>
          -- break
          simp only [Bool.not_false]
          (try bool_if)
          wp_auto
          wp_for_post
          isplitl []
          · itrivial
          iexists L3
          iframe
          ipureintro
          exact Hperm3
        simp only [Bool.not_true]
        (try bool_if)
        wp_auto
        wp_apply wp_any_Swap x R L3 jl (jl - W64 1) y0 y1 (by word) (by word)
          Hy0_lookup Hy1_lookup $$ [$Hs $Hl] as %L4 ⟨Hl, %HP4⟩
        wp_for_post
        iframe
        iexists (jl - W64 1), _
        iframe
        ipureintro
        exact ⟨by word, by word, Hperm3.trans HP4⟩
      · isplitl []
        · itrivial
        iexists L2
        iframe
        ipureintro
        exact Hperm2
    clear Hperm2 hlen2
    iintro %v ⟨%Hv, HQ⟩
    subst Hv
    icases HQ with ⟨%L3, HQ⟩
    iNamed HQ
    wp_auto
    wp_if_destruct
    · ihave HRt : (∃ (jr : w64) (L4 : List E),
          "jr" ∷ j_ptr ↦ jr ∗
          "Hl" ∷ R L4 ∗
          "%jrange" ∷ ⌜sint.Z i_val < sint.Z jr ∧ sint.Z jr ≤ sint.Z b ∧ l.Perm L4⌝ : IProp GF)
          $$ [j Hl]
      · iexists _, L3
        iframe
        ipureintro
        exact ⟨by word, by word, Hperm3⟩
      clear Hperm3
      wp_for HRt
      obtain ⟨Hj1, Hj2, Hperm4⟩ := jrange
      have hlen4 := Hperm4.length_eq
      wp_if_destruct
      · list_elem L4 (sint.nat jr) as y0
        list_elem L4 (sint.nat (jr - W64 1)) as y1
        wp_apply wp_any_Less x R L4 jr (jr - W64 1) y0 y1 (by word) (by word)
          Hy0_lookup Hy1_lookup $$ [$Hs $Hl] as %r' Hl
        cases r'
        case false =>
          -- break
          simp only [Bool.not_false]
          (try bool_if)
          wp_auto
          wp_for_post
          wp_for_post
          iframe
          iexists (jc + W64 1), i_val, L4
          iframe
          ipureintro
          exact ⟨by word, by word, Hperm4⟩
        simp only [Bool.not_true]
        (try bool_if)
        wp_auto
        wp_apply wp_any_Swap x R L4 jr (jr - W64 1) y0 y1 (by word) (by word)
          Hy0_lookup Hy1_lookup $$ [$Hs $Hl] as %L5 ⟨Hl, %HP5⟩
        wp_for_post
        iframe
        iexists (jr + W64 1), _
        iframe
        ipureintro
        exact ⟨by word, by word, Hperm4.trans HP5⟩
      · wp_for_post
        iframe
        iexists (jc + W64 1), i_val, L4
        iframe
        ipureintro
        exact ⟨by word, by word, Hperm4⟩
    · wp_for_post
      iframe
      iexists (jc + W64 1), i_val, L3
      iframe
      ipureintro
      exact ⟨by word, by word, Hperm3⟩
  · -- `i = b`: return true
    have hib : i_val = b := by word
    subst hib
    rw [decide_eq_true rfl]
    wp_auto
    wp_for_post
    iapply HΦ
    iframe
    ipureintro
    exact HP1

end proof

end EtcdGrove
end Perennial
