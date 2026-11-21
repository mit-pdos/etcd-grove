/-
The proof of `sort.rotate` (`Spec/sort/rotate.lean`): its loop computes `stableModel.rotLoop`.
-/
module

public import Spec.sort.rotate
public import Spec.sort.swapRange

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

theorem sort.rotate.wp_proof (wp_swapRange : sort.swapRange.spec (GF := GF) (hG := hG)) :
    sort.rotate.spec (GF := GF) (hG := hG) := fun E x R lt l a m b => by
  wp_start as ⟨#Hs, Hl, %Hb⟩
  wp_auto
  ihave HI : (∃ (i j : w64) (L : List E),
      "i" ∷ i_ptr ↦ i ∗
      "j" ∷ j_ptr ↦ j ∗
      "Hl" ∷ R L ∗
      "%Hi" ∷ ⌜0 < sint.Z i ∧ sint.Z i ≤ sint.Z m - sint.Z a ∧ 0 < sint.Z j ∧
        sint.Z j ≤ sint.Z b - sint.Z m ∧ L.length = l.length ∧
        rotLoop L (sint.nat m) (sint.nat i) (sint.nat j) =
          rotateM l (sint.nat a) (sint.nat m) (sint.nat b)⌝ : IProp GF) $$ [i j Hl]
  · iexists (m - a), (b - m), l
    iframe
    ipureintro
    refine ⟨by word, by word, by word, by word, rfl, ?_⟩
    unfold rotateM
    rw [show sint.nat (m - a) = sint.nat m - sint.nat a by word,
      show sint.nat (b - m) = sint.nat b - sint.nat m by word]
  wp_for HI
  obtain ⟨Hi1, Hi2, Hj1, Hj2, HL, Heq⟩ := Hi
  wp_if_destruct
  · have hne : i ≠ j := by
      intro h; subst h; simp at Hif; exact false_neq_true Hif
    clear Hif
    have hne' : sint.Z i ≠ sint.Z j := fun h => hne (by word)
    wp_if_destruct
    · -- `i > j`: swap `[m-i, m-i+j)` with `[m, m+j)`
      wp_apply wp_swapRange E x R lt L (m - i) m j $$ [Hl] as Hl
      · iframe Hl; iframe #; ipureintro; word
      wp_for_post
      iframe
      iexists (i - j), j, _
      iframe
      ipureintro
      refine ⟨by word, by word, by word, by word, by rw [swapRangeM_length]; exact HL, ?_⟩
      rw [← Heq]
      conv => rhs; unfold rotLoop
      rw [dif_neg (by word), if_neg (by word), dif_pos (by word)]
      rw [show sint.nat (i - j) = sint.nat i - sint.nat j by word,
        show sint.nat (m - i) = sint.nat m - sint.nat i by word]
    · -- `i < j`: swap `[m-i, m)` with `[m+j-i, m+j)`
      wp_apply wp_swapRange E x R lt L (m - i) (m + j - i) i $$ [Hl] as Hl
      · iframe Hl; iframe #; ipureintro; word
      wp_for_post
      iframe
      iexists i, (j - i), _
      iframe
      ipureintro
      refine ⟨by word, by word, by word, by word, by rw [swapRangeM_length]; exact HL, ?_⟩
      rw [← Heq]
      conv => rhs; unfold rotLoop
      rw [dif_neg (by word), if_neg (by word), dif_neg (by word)]
      rw [show sint.nat (j - i) = sint.nat j - sint.nat i by word,
        show sint.nat (m - i) = sint.nat m - sint.nat i by word,
        show sint.nat (m + j - i) = sint.nat m + sint.nat j - sint.nat i by word]
  · -- `i == j`: the last swap
    have hij : i = j := by
      apply Classical.byContradiction; intro h
      exact Hif (by simp [h])
    subst hij
    simp only [decide_true, Bool.not_true, ↓reduceIte]
    wp_auto
    wp_apply wp_swapRange E x R lt L (m - i) m i $$ [Hl] as Hl
    · iframe Hl; iframe #; ipureintro; word
    iapply HΦ
    rw [← Heq]
    unfold rotLoop
    rw [dif_neg (by word), if_pos rfl,
      show sint.nat (m - i) = sint.nat m - sint.nat i by word]
    iexact Hl
