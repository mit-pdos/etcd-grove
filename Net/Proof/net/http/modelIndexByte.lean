/-
The proof of `modelIndexByte` (`Net/Spec/net/http/modelIndexByte.lean`): the loop finds the first `c`.
-/
module

public import Net.Spec.net.http.modelIndexByte
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.perennial.goose.model.strings (wp_string_len)

namespace net.http

theorem idxByte_found (s : List w8) (c : w8) (i : Nat) (hi : i < s.length) (h : s[i]? = some c)
    (hb : ∀ j, j < i → s[j]? ≠ some c) : idxByte s c = W64 (i : Int) := by
  have : s.findIdx? (· = c) = some i := by
    rw [List.findIdx?_eq_some_iff_getElem]
    refine ⟨hi, ?_, fun j hj => ?_⟩
    · rw [List.getElem?_eq_getElem hi] at h; simpa using h
    · have := hb j hj
      rw [List.getElem?_eq_getElem (by omega)] at this; simpa using this
  simp [idxByte, this]

theorem idxByte_none (s : List w8) (c : w8) (hb : ∀ j, j < s.length → s[j]? ≠ some c) :
    idxByte s c = W64 (-1) := by
  have : s.findIdx? (· = c) = none := by
    rw [List.findIdx?_eq_none_iff]
    intro x hx
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
    have := hb j hj
    rw [List.getElem?_eq_getElem hj] at this; simpa using this
  simp [idxByte, this]

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.http.Assumptions]

theorem modelIndexByte.wp_proof : modelIndexByte.spec (GF := GF) (hG := hG) := by
  intro s c
  wp_start
  wp_auto
  ihave HI : (∃ (i : w64), "i" ∷ i_ptr ↦ i ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.nat i ≤ s.length ∧
        ∀ j, j < sint.nat i → s[j]? ≠ some c⌝ : IProp GF) $$ [i]
  · iexists W64 0
    iframe
    ipureintro
    refine ⟨by word, by word, fun j hj => ?_⟩
    exfalso; revert hj; word
  wp_for HI
  wp_apply wp_string_len as %Hl
  have hlen : sint.Z (W64 (s.length : Int)) = s.length := by word
  by_cases hlt : sint.Z i < sint.Z (W64 (s.length : Int))
  · simp only [hlt, _root_.decide_true, false_neq_true, true_neq_false, decide_false, ↓reduceIte]
    have hi : sint.nat i < s.length := by word
    obtain ⟨x, hx⟩ : ∃ x, s[sint.nat i]? = some x := ⟨_, List.getElem?_eq_getElem hi⟩
    wp_auto
    rw [ite_eq_left_of_eq_true _ _ (eq_true Hi.1), hx]
    wp_auto
    by_cases hxc : x = c
    · simp only [decide_eq_true hxc, ↓reduceIte]
      wp_auto
      wp_for_post
      have hiv : i = W64 ((sint.nat i : Nat) : Int) := by word
      rw [idxByte_found s c (sint.nat i) hi (hxc ▸ hx) Hi.2.2, ← hiv]
      iapply HΦ; ipureintro; exact Hl
    · simp only [decide_eq_false hxc, Bool.false_eq_true, ↓reduceIte]
      wp_auto
      wp_for_post
      iframe
      iexists _
      iframe
      ipureintro
      have hz : 0 ≤ sint.Z (i + W64 1) := by word
      have hn : sint.nat (i + W64 1) = sint.nat i + 1 := by word
      rw [hn]
      refine ⟨hz, by omega, fun j hj => ?_⟩
      rcases Nat.lt_or_ge j (sint.nat i) with h | h
      · exact Hi.2.2 j h
      · have : j = sint.nat i := by omega
        subst this; rw [hx]; simpa using hxc
  · simp only [hlt, decide_false, false_neq_true, true_neq_false, _root_.decide_true,
      Bool.false_eq_true, ↓reduceIte]
    wp_auto
    have hi : sint.nat i = s.length := by word
    rw [idxByte_none s c (fun j hj => Hi.2.2 j (by omega))]
    iapply HΦ; ipureintro; exact Hl

end proof

end net.http
end Perennial
