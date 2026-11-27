/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/sortUint64s.lean (241f27e).
-/
/-
The proof of `raft.sortUint64s`: an insertion sort over a `[]uint64`, with the nested
three-clause loops Goose produces (`doFor`). Reuses the pure insertion-sort facts of
`Perennial.slices` (`IsSortedSeg`, `InsBr`, `OutsideSame`, ...).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.sortUint64s
public import Perennial.Proof.slices.InsertionSortBasics

@[expose] public section

set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Perennial.slices

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

/-- Bridge the perennial `is_sorted` (relational) to `List.Pairwise (·≤·)`. -/
theorem is_sorted_unsigned_pairwise (l : List w64)
    (H : slices.is_sorted (fun a b => uint.Z a < uint.Z b) l) :
    List.Pairwise (fun x y => uint.Z x ≤ uint.Z y) l := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  have := H i j l[i] l[j] hij (by rw [List.getElem?_eq_getElem hi])
    (by rw [List.getElem?_eq_getElem hj])
  omega

theorem github_com.hashicorp.raft.sortUint64s.wp_proof :
    github_com.hashicorp.raft.sortUint64s.spec (GF := GF) (hG := hG) :=
  fun s xs => by
  haveI swo : StrictWeakOrder (fun (a b : w64) => uint.Z a < uint.Z b) :=
    StrictWeakOrder_unsigned_lt
  wp_start as H
  iNamed H
  wp_auto
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  ihave HI1 : (∃ (i_val : w64) (xs' : List w64),
      "i" ∷ i_ptr ↦ i_val ∗
      "Hs" ∷ s ↦* xs' ∗
      "%irange" ∷ ⌜1 ≤ sint.Z i_val ∧ sint.Z i_val ≤ Max.max 1 (sint.Z s.len)⌝ ∗
      "%HPerm1" ∷ ⌜xs ≡ₚ xs'⌝ ∗
      "%Hsorted" ∷ ⌜IsSortedSeg (fun a b => uint.Z a < uint.Z b) xs' 0 (sint.nat i_val)⌝ ∗
      "%Houtside1" ∷ ⌜OutsideSame xs xs' 0 (sint.nat s.len)⌝ : IProp GF) $$ [i Hs]
  · iexists (W64 1), xs
    iframe
    ipureintro
    refine ⟨⟨by word, by word⟩, List.Perm.refl _, ?_, outsideSame_refl _ _ _⟩
    rw [show sint.nat (W64 1) = 0 + 1 by word]
    exact isSortedSeg_one _ xs 0
  wp_for HI1
  by_cases Hif : sint.Z i_val < sint.Z s.len
  · simp only [Hif, _root_.decide_true, ↓reduceIte]
    wp_auto
    have Hilt : sint.Z i_val < sint.Z s.len := Hif
    have hlen' := HPerm1.length_eq
    ihave HI2 : (∃ (j_val : w64) (xs'' : List w64),
        "j" ∷ j_ptr ↦ j_val ∗
        "Hs" ∷ s ↦* xs'' ∗
        "%jrange" ∷ ⌜0 ≤ sint.Z j_val ∧ sint.Z j_val ≤ sint.Z i_val⌝ ∗
        "%Hperm2" ∷ ⌜xs ≡ₚ xs''⌝ ∗
        "%HsortedBr" ∷ ⌜InsBr (fun a b => uint.Z a < uint.Z b) xs'' 0 (sint.nat i_val) (sint.nat j_val)⌝ ∗
        "%Houtside2" ∷ ⌜OutsideSame xs xs'' 0 (sint.nat s.len)⌝ : IProp GF) $$ [j Hs]
    · iexists _, xs'
      iframe
      ipureintro
      exact ⟨⟨by word, by word⟩, HPerm1, insBr_init _ _ _ _ Hsorted, Houtside1⟩
    wp_for HI2
    have hlen'' := Hperm2.length_eq
    wp_if_destruct
    · -- j > 0: evaluate a[j] < a[j-1]
      have hjpos : 0 < sint.Z j_val := by word
      have hj1 : sint.nat (j_val - W64 1) = sint.nat j_val - 1 := by word
      list_elem xs'' (sint.nat j_val) as x0
      list_elem xs'' (sint.nat (j_val - W64 1)) as x1
      slice_index_if
      wp_apply wp_load_slice_index s (sint.Z j_val) xs'' _ x0 (by word) $$ [Hs] with Hs
      · iframe Hs; ipureintro; exact Hx0_lookup
      slice_index_if
      wp_apply wp_load_slice_index s (sint.Z (j_val - W64 1)) xs'' _ x1 (by word) $$ [Hs] with Hs
      · iframe Hs; ipureintro; exact Hx1_lookup
      wp_if_destruct
      · -- a[j] < a[j-1]: swap and continue the inner loop
        have hR : uint.Z x0 < uint.Z x1 := of_decide_eq_true (GoGlobalContext.intoVal_inj_bool Hif)
        slice_index_if; wp_auto
        slice_index_if; wp_auto
        slice_index_if
        wp_apply wp_load_slice_index s (sint.Z (j_val - W64 1)) xs'' _ x1 (by word) $$ [Hs] with Hs
        · iframe Hs; ipureintro; exact Hx1_lookup
        slice_index_if
        wp_apply wp_load_slice_index s (sint.Z j_val) xs'' _ x0 (by word) $$ [Hs] with Hs
        · iframe Hs; ipureintro; exact Hx0_lookup
        wp_apply wp_store_slice_index s (sint.Z j_val) xs'' x1 $$ [Hs] with Hs
        · iframe Hs; ipureintro; rw [← hlen'', Hlen.1]
          refine ⟨by word, ?_⟩; simp only [sint.nat]; word
        wp_apply wp_store_slice_index s (sint.Z (j_val - W64 1)) _ x0 $$ [Hs] with Hs
        · iframe Hs; ipureintro; rw [List.length_set, ← hlen'', Hlen.1]
          refine ⟨by word, ?_⟩; simp only [sint.nat]; word
        wp_for_post
        iframe
        iexists (j_val - W64 1), _
        iframe
        ipureintro
        have hset : (sint.Z (j_val - W64 1)).toNat = sint.nat j_val - 1 := by
          simp only [sint.nat]; word
        have hsetj : (sint.Z j_val).toNat = sint.nat j_val := rfl
        rw [hset, hsetj]
        rw [hj1] at Hx1_lookup
        refine ⟨⟨by word, by word⟩, ?_, ?_, ?_⟩
        · exact Hperm2.trans (swap_perm xs'' (sint.nat j_val - 1) (sint.nat j_val) x1 x0 Hx1_lookup Hx0_lookup)
        · rw [show sint.nat (j_val - W64 1) = sint.nat j_val - 1 from hj1]
          exact insBr_swap (fun a b => uint.Z a < uint.Z b) xs'' 0 (sint.nat i_val) (sint.nat j_val)
            x0 x1 HsortedBr (by word) (by word) Hx0_lookup Hx1_lookup hR
        · exact outsideSame_trans _ _ _ _ _ Houtside2
            (outsideSame_swap xs'' (sint.nat j_val - 1) (sint.nat j_val) x1 x0 0 (sint.nat s.len)
              ⟨by word, by word⟩ ⟨by word, by word⟩)
      · -- ¬ (a[j] < a[j-1]): inner loop exits, continue outer loop
        have hR : ¬ uint.Z x0 < uint.Z x1 := by
          intro h; apply Hif; rw [decide_eq_true_eq.mpr h]
        simp only [decide_eq_false hR, Bool.false_eq_true, ↓reduceIte]
        rw [hj1] at Hx1_lookup
        have Hs2 := insBr_done_cmp (fun a b => uint.Z a < uint.Z b) xs'' 0 (sint.nat i_val)
          (sint.nat j_val) x0 x1 HsortedBr (by word) (by word) Hx0_lookup Hx1_lookup hR
        wp_for_post
        iframe
        iexists (i_val + W64 1), xs''
        iframe
        ipureintro
        rw [show sint.nat (i_val + W64 1) = sint.nat i_val + 1 by word]
        exact ⟨⟨by word, by word⟩, Hperm2, Hs2, Houtside2⟩
    · -- j ≤ 0 (so j = 0): inner loop exits, continue outer loop
      have Hs2 := insBr_done_a (fun a b => uint.Z a < uint.Z b) xs'' 0 (sint.nat i_val)
        (sint.nat j_val) HsortedBr (by word)
      wp_for_post
      iframe
      iexists (i_val + W64 1), xs''
      iframe
      ipureintro
      rw [show sint.nat (i_val + W64 1) = sint.nat i_val + 1 by word]
      exact ⟨⟨by word, by word⟩, Hperm2, Hs2, Houtside2⟩
  · -- i ≥ len: outer loop exits
    simp only [Hif, decide_false, Bool.false_eq_true, ↓reduceIte]
    wp_auto
    iapply HΦ
    iframe
    ipureintro
    refine ⟨HPerm1, is_sorted_unsigned_pairwise _ ?_⟩
    apply isSortedSeg_is_sorted
    have e : xs'.length = sint.nat s.len := by rw [← HPerm1.length_eq]; exact Hlen.1
    have hle : xs'.length ≤ sint.nat i_val := by rw [e]; word
    exact isSortedSeg_mono (fun a b => uint.Z a < uint.Z b) xs' 0 (sint.nat i_val) xs'.length hle Hsorted

end proof

end Perennial
