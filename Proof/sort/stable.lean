/-
The proof of `sort.stable` (`Spec/sort/stable.lean`): its loops compute `stableModel.insPhase`,
`stableModel.mergePhase` and `stableModel.mergeLevel`.
-/
module

public import Spec.sort.stable
public import Spec.sort.insertionSort
public import Spec.sort.symMerge

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

set_option maxHeartbeats 4000000 in
theorem sort.stable.wp_proof
    (wp_insertionSort : EtcdGrove.sort.insertionSort.spec (GF := GF) (hG := hG))
    (wp_symMerge : sort.symMerge.spec (GF := GF) (hG := hG)) :
    sort.stable.spec (GF := GF) (hG := hG) := fun E x R lt l n => by
  wp_start as ⟨#Hs, Hl, %Hn⟩
  wp_auto
  -- the insertion sorts of the blocks of 20
  ihave HI : (∃ (av bv : w64) (L : List E),
      "a" ∷ a_ptr ↦ av ∗
      "b" ∷ b_ptr ↦ bv ∗
      "Hl" ∷ R L ∗
      "%Hab" ∷ ⌜sint.Z bv = sint.Z av + 20 ∧ 0 ≤ sint.Z av ∧ sint.Z av ≤ sint.Z n ∧
        L.length = l.length ∧
        mergePhase lt l.length 20 (insPhase lt l.length (sint.nat av) L) =
          stableM lt l l.length⌝ : IProp GF) $$ [a b Hl]
  · iexists (W64 0), (W64 20), l
    iframe
    ipureintro
    refine ⟨by word, by word, by word, rfl, ?_⟩
    rw [show sint.nat (W64 0) = 0 by word]; rfl
  wp_for HI
  obtain ⟨Hab1, Hab2, Hab3, HL, Heq⟩ := Hab
  wp_if_destruct
  · wp_apply wp_insertionSort E x R lt L av bv $$ [Hl] as Hl
    · iframe Hl; iframe #; ipureintro; word
    wp_for_post
    iframe
    iexists bv, (bv + W64 20), _
    iframe
    ipureintro
    refine ⟨by word, by word, by word, ?_, ?_⟩
    · rw [insertionSortM_length, HL]
    · rw [← Heq]
      congr 1
      conv => rhs; unfold insPhase
      rw [dif_pos (by word), show sint.nat bv = sint.nat av + 20 by word]
  -- the last block
  wp_apply wp_insertionSort E x R lt L av n $$ [Hl] as Hl
  · iframe Hl; iframe #; ipureintro; word
  have hn : sint.nat n = l.length := by word
  have Heq2 : mergePhase lt l.length 20 (insertionSortM lt L (sint.nat av) (sint.nat n)) =
      stableM lt l l.length := by
    rw [← Heq, hn]; congr 1
    conv => rhs; unfold insPhase
    rw [dif_neg (by word)]
  have HL2 : (insertionSortM lt L (sint.nat av) (sint.nat n)).length = l.length := by
    rw [insertionSortM_length, HL]
  generalize insertionSortM lt L (sint.nat av) (sint.nat n) = L0 at Heq2 HL2 ⊢
  clear Heq HL Hab1 Hab2 Hab3 Hif
  -- the merges, doubling `blockSize`
  ihave HM : (∃ (bs av bv : w64) (L : List E),
      "blockSize" ∷ blockSize_ptr ↦ bs ∗
      "a" ∷ a_ptr ↦ av ∗
      "b" ∷ b_ptr ↦ bv ∗
      "Hl" ∷ R L ∗
      "%Hbs" ∷ ⌜0 < sint.Z bs ∧ sint.Z bs % 20 = 0 ∧ L.length = l.length ∧
        mergePhase lt l.length (sint.nat bs) L = stableM lt l l.length⌝ : IProp GF)
      $$ [blockSize a b Hl]
  · iexists (W64 20), av, bv, L0
    iframe
    ipureintro
    refine ⟨by word, by word, HL2, ?_⟩
    rw [show sint.nat (W64 20) = 20 by word]; exact Heq2
  wp_for HM
  obtain ⟨Hbs1, Hbs2, HL, Heq⟩ := Hbs
  wp_if_destruct
  · -- one level: `symMerge(a, a+bs, a+2bs)` for every pair of blocks
    have h2bs : sint.Z (W64 2 * bs) = 2 * sint.Z bs := by word
    ihave HL : (∃ (av bv : w64) (L' : List E),
        "a" ∷ a_ptr ↦ av ∗
        "b" ∷ b_ptr ↦ bv ∗
        "Hl" ∷ R L' ∗
        "%Hab" ∷ ⌜sint.Z bv = sint.Z av + 2 * sint.Z bs ∧ 0 ≤ sint.Z av ∧ sint.Z av ≤ sint.Z n ∧
          L'.length = l.length ∧
          mergePhase lt l.length (2 * sint.nat bs) (mergeLevel lt l.length (sint.nat bs)
            (sint.nat av) L') = stableM lt l l.length⌝ : IProp GF) $$ [a b Hl]
    · iexists (W64 0), (W64 2 * bs), L
      iframe
      ipureintro
      refine ⟨by word, by word, by word, HL, ?_⟩
      rw [← Heq, show sint.nat (W64 0) = 0 by word]
      conv => rhs; unfold mergePhase
      rw [dif_pos ⟨by word, by word⟩]
    wp_for HL
    obtain ⟨Hab1, Hab2, Hab3, HL', Heq'⟩ := Hab
    wp_if_destruct
    · wp_apply wp_symMerge E x R lt L' av (av + bs) bv $$ [Hl] as Hl
      · iframe Hl; iframe #; ipureintro; word
      wp_for_post
      iframe
      iexists bv, (bv + W64 2 * bs), _
      iframe
      ipureintro
      have h20 : (2 : Int) ^ 61 % 20 ≠ 0 := by decide
      refine ⟨by word, by word, by word, by rw [symMergeM_length, HL'], ?_⟩
      rw [← Heq']
      congr 1
      conv => rhs; unfold mergeLevel
      rw [dif_pos ⟨by word, by word⟩, show sint.nat bv = sint.nat av + 2 * sint.nat bs by word,
        show sint.nat (av + bs) = sint.nat av + sint.nat bs by word]
    · -- the last pair, if it has a second block
      have hlevel : ∀ c : Prop, ∀ _ : Decidable c,
          (c ↔ sint.nat av + sint.nat bs < l.length) →
          mergeLevel lt l.length (sint.nat bs) (sint.nat av) L' =
            if c then symMergeM lt L' (sint.nat av) (sint.nat av + sint.nat bs) l.length
            else L' := by
        intro c _ hc
        unfold mergeLevel
        rw [dif_neg (by word)]
        by_cases h : c
        · rw [if_pos h, if_pos (hc.1 h)]
        · rw [if_neg h, if_neg (fun h' => h (hc.2 h'))]
      by_cases hm : sint.Z (av + bs) < sint.Z n
      · simp only [hm, decide_true]
        wp_auto
        wp_apply wp_symMerge E x R lt L' av (av + bs) n $$ [Hl] as Hl
        · iframe Hl; iframe #; ipureintro; word
        wp_for_post
        iframe
        iexists (bs * W64 2), av, bv, _
        iframe
        ipureintro
        refine ⟨by word, by word, by rw [symMergeM_length, HL'], ?_⟩
        have hc : sint.nat av + sint.nat bs < l.length := by word
        rw [← Heq', hlevel True inferInstance (by simp [hc]), if_pos trivial,
          show sint.nat (bs * W64 2) = 2 * sint.nat bs by word,
          show sint.nat (av + bs) = sint.nat av + sint.nat bs by word, hn]
      · simp only [hm, decide_false]
        wp_auto
        wp_for_post
        iframe
        iexists (bs * W64 2), av, bv, L'
        iframe
        ipureintro
        refine ⟨by word, by word, HL', ?_⟩
        have hc : ¬ sint.nat av + sint.nat bs < l.length := by word
        rw [← Heq', hlevel False inferInstance (by simp [hc]), if_neg id,
          show sint.nat (bs * W64 2) = 2 * sint.nat bs by word]
  · iapply HΦ
    rw [← Heq]
    unfold mergePhase
    rw [dif_neg (by word)]
    iexact Hl
