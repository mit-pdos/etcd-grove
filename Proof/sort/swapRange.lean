/-
The proof of `sort.swapRange` (`Spec/sort/swapRange.lean`): its loop computes
`stableModel.swapRangeM`.
-/
module

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

theorem sort.swapRange.wp_proof : sort.swapRange.spec (GF := GF) (hG := hG) :=
    fun E x R lt l a b n => by
  wp_start as ⟨#Hs, Hl, %Hb⟩
  ihave #Hsrt := sorterSpec_isSorter x R lt $$ Hs
  wp_auto
  ihave HI : (∃ (i : w64),
      "i" ∷ i_ptr ↦ i ∗
      "Hl" ∷ R (swapRangeM l (sint.nat a) (sint.nat b) (sint.nat i)) ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z n⌝ : IProp GF) $$ [i Hl]
  · iexists (W64 0)
    rw [show sint.nat (W64 0) = 0 by word]
    simp only [swapRangeM]
    iframe
    ipureintro; word
  wp_for HI
  have hlen := swapRangeM_length l (sint.nat a) (sint.nat b) (sint.nat i)
  wp_if_destruct
  · list_elem (swapRangeM l (sint.nat a) (sint.nat b) (sint.nat i)) (sint.nat (a + i)) as x0
    list_elem (swapRangeM l (sint.nat a) (sint.nat b) (sint.nat i)) (sint.nat (b + i)) as x1
    wp_apply _root_.Perennial.sort.wp_sorter_Swap x R (fun a b => lt a b = true) _ (a + i) (b + i)
      x0 x1 (by word) (by word) Hx0_lookup Hx1_lookup $$ [$Hsrt $Hl] as Hl
    have heq : swapRangeM l (sint.nat a) (sint.nat b) (sint.nat (i + W64 1)) =
        <[sint.nat (a + i) := x1]> (<[sint.nat (b + i) := x0]>
          (swapRangeM l (sint.nat a) (sint.nat b) (sint.nat i))) := by
      rw [show sint.nat (i + W64 1) = sint.nat i + 1 by word]
      simp only [swapRangeM]
      have e1 : sint.nat (a + i) = sint.nat a + sint.nat i := by word
      have e2 : sint.nat (b + i) = sint.nat b + sint.nat i := by word
      simp only [e1, e2] at Hx0_lookup Hx1_lookup ⊢
      rw [swapL_eq _ _ _ _ _ Hx0_lookup Hx1_lookup]
      exact _root_.Perennial.sort.swap_set_comm _ _ _ _ _ Hx0_lookup Hx1_lookup
    wp_for_post
    iframe
    iexists (i + W64 1)
    rw [heq]
    iframe
    ipureintro
    word
  · have : sint.Z i = sint.Z n := by omega
    rw [show sint.nat i = sint.nat n by word]
    iapply HΦ
    iframe
