/-
The proof of `modelHeaderValueContainsToken` (`Net/Spec/net/http/modelHeaderValueContainsToken.lean`):
the comma `modelIndexByte` finds is an index of the string (`idxByte_cases`), so both slices are in
bounds.
-/
module

public import Net.Spec.net.http.modelHeaderValueContainsToken
public import Net.Spec.net.http.modelIndexByte
public import Net.Spec.net.http.modelTrimOWS
public import Net.Spec.net.http.modelTokenEqual
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.perennial.goose.model.strings (wp_string_len)

namespace net.http

/-- `idxByte s c` is `-1` or an index of `s`. -/
theorem idxByte_cases (s : List w8) (c : w8) :
    idxByte s c = W64 (-1) ∨ ∃ i, i < s.length ∧ idxByte s c = W64 (i : Int) := by
  unfold idxByte
  split
  · rename_i i h
    right
    exact ⟨i, (List.findIdx?_eq_some_iff_getElem.1 h).1, rfl⟩
  · left; rfl

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.http.Assumptions]

theorem modelHeaderValueContainsToken.wp_proof
    (wp_idx : modelIndexByte.spec (GF := GF) (hG := hG))
    (wp_trim : modelTrimOWS.spec (GF := GF) (hG := hG))
    (wp_teq : modelTokenEqual.spec (GF := GF) (hG := hG)) :
    modelHeaderValueContainsToken.spec (GF := GF) (hG := hG) := by
  intro v0 token
  wp_start
  wp_auto
  wp_apply (wp_idx v0 (W8 44)) as %Hl0
  ihave HI : (∃ (v' : GoString), "v" ∷ v_ptr ↦ v' ∗ "comma" ∷ comma_ptr ↦ idxByte v' (W8 44) ∗
      "%Hl" ∷ ⌜v'.length < 2 ^ 63⌝ : IProp GF) $$ [v comma]
  · iexists v0
    iframe
    ipureintro; exact Hl0
  wp_for HI
  have hcase : idxByte v' (W8 44) = W64 (-1) ∨
      ∃ i, i < v'.length ∧ idxByte v' (W8 44) = W64 (i : Int) ∧ W64 (i : Int) ≠ W64 (-1) := by
    rcases idxByte_cases v' (W8 44) with hc | ⟨i, hi, hc⟩
    · exact Or.inl hc
    · by_cases hm : W64 (i : Int) = W64 (-1)
      · exact Or.inl (hc.trans hm)
      · exact Or.inr ⟨i, hi, hc, hm⟩
  rcases hcase with hc | ⟨i, hi, hc, hm⟩
  · rw [hc]
    simp only [_root_.decide_true, Bool.not_true]
    rw [if_neg (by simp [false_neq_true]), if_pos (by simp)]
    wp_auto
    wp_apply (wp_trim v')
    wp_apply (wp_teq _ token) as %b0
    iintro -
    wp_auto
    iapply HΦ; itrivial
  · rw [hc]
    simp only [decide_eq_false hm, Bool.not_false]
    rw [if_pos (by simp)]
    wp_auto
    have hiz : sint.Z (W64 (i : Int)) = i := by word
    have h0 : sint.Z (W64 0) = 0 := rfl
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by rw [hiz, h0]; omega, by rw [hiz]; omega⟩)]
    wp_apply (wp_trim _)
    wp_apply (wp_teq _ token) as %b0
    iintro -
    wp_if_destruct
    · wp_apply (wp_string_len v' (t := go.string)) as %-
      have h1 : sint.Z (W64 (i : Int) + W64 1) = i + 1 := by word
      have hlz : sint.Z (W64 (v'.length : Int)) = v'.length := by word
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by rw [h1]; omega, by rw [h1, hlz]; omega,
        by rw [hlz]; exact Int.le_refl _⟩)]
      wp_auto
      wp_for_post
      wp_apply (wp_idx _ (W8 44)) as %Hl1
      iframe
      iexists _
      iframe
      ipureintro; exact Hl1
    · wp_for_post
      iapply HΦ; itrivial

end proof

end net.http
end Perennial
