/-
The proof of `endsInNumber` (`Spec/encoding/json/Codec/endsInNumber.lean`): the loop's index `i`
is read only below `len(b)` (it may step past it by two, after an escape), and `b[len(b)-1]` only
when `b` is not empty.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.encoding.json.Codec.endsInNumber

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace encoding.json

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : encoding.json.Assumptions]

theorem endsInNumber.wp_proof : endsInNumber.spec (GF := GF) (hG := hG) := by
  intro b dq bs hlen
  wp_start as Hs
  wp_auto
  ihave %Hs_len := ownSlice_len _ _ _ $$ Hs
  ihave HI : (∃ (i : w64) (st : Bool),
      "i" ∷ i_ptr ↦ i ∗ "inStr" ∷ inStr_ptr ↦ st ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z b.len + 1⌝ : IProp GF) $$ [i inStr]
  · iexists (W64 0), false
    iframe
    ipureintro
    exact ⟨by decide, by have := Hs_len.2; rw [show sint.Z (W64 0) = 0 from rfl]; omega⟩
  wp_for HI
  wp_if_destruct
  · have Hif' : sint.Z i < sint.Z b.len := by simpa using Hif
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hi.1, Hif'⟩)]
    have hlt : (sint.Z i).toNat < bs.length := by
      rw [Hs_len.1]; exact (Int.toNat_lt_toNat (Int.lt_of_le_of_lt Hi.1 Hif')).2 Hif'
    obtain ⟨x, Hx⟩ : ∃ x, bs[(sint.Z i).toNat]? = some x := ⟨_, List.getElem?_eq_getElem hlt⟩
    wp_apply wp_load_slice_index _ _ _ _ x Hi.1 $$ [Hs] with Hs
    · iframe; ipureintro; exact Hx
    have h1 : sint.Z (i + W64 1) = sint.Z i + 1 := by word
    wp_join iprop(∃ (i' : w64) (st' : Bool), c_ptr ↦ x ∗ i_ptr ↦ i' ∗ inStr_ptr ↦ st' ∗
        ⌜sint.Z i' = sint.Z i ∨ sint.Z i' = sint.Z i + 1⌝) with [c i inStr]
      as ⟨%i', %st', c, i, inStr, %Hi'⟩
    · wp_if_destruct <;>
      · isplitl []
        · ipureintro; first | rfl | trivial
        iexists _, _
        iframe
        ipureintro; left; rfl
    · wp_if_destruct
      · isplitl []
        · ipureintro; first | rfl | trivial
        iexists _, _
        iframe
        ipureintro; right; exact h1
      · wp_if_destruct <;>
        · isplitl []
          · ipureintro; first | rfl | trivial
          iexists _, _
          iframe
          ipureintro; left; rfl
    have h3 : sint.Z (i' + W64 1) = sint.Z i' + 1 := by
      have : sint.Z i' ≤ sint.Z i + 1 := by omega
      have : sint.Z i < 2 ^ 62 := by omega
      word
    wp_for_post
    iframe
    iexists _, st'
    iframe
    ipureintro
    constructor <;> omega
  cases st
  · wp_auto
    wp_if_destruct
    · iapply HΦ $$ Hs
    · have hne : b.len ≠ W64 0 := Hif
      have hpos : 0 < sint.Z b.len := by
        have := Hs_len.2
        rcases Int.lt_or_eq_of_le this with h | h
        · exact h
        · exact absurd (by word) hne
      have hk : sint.Z (b.len - W64 1) = sint.Z b.len - 1 := by word
      have hlt : (sint.Z (b.len - W64 1)).toNat < bs.length := by
        rw [Hs_len.1, hk, show sint.nat b.len = (sint.Z b.len).toNat from rfl]; omega
      obtain ⟨x, Hx⟩ : ∃ x, bs[(sint.Z (b.len - W64 1)).toNat]? = some x :=
        ⟨_, List.getElem?_eq_getElem hlt⟩
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by rw [hk]; omega, by rw [hk]; omega⟩)]
      wp_apply wp_load_slice_index _ _ _ _ x (by rw [hk]; omega) $$ [Hs] with Hs
      · iframe; ipureintro; exact Hx
      wp_if_destruct <;> iapply HΦ $$ Hs
  · wp_auto
    iapply HΦ $$ Hs

end proof

end encoding.json
end Perennial
