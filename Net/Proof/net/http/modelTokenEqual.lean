/-
The proof of `modelTokenEqual` (`Net/Spec/net/http/modelTokenEqual.lean`): after the length check, the
loop's indices are in both strings.
-/
module

public import Net.Spec.net.http.modelTokenEqual
public import Net.Spec.net.http.modelLowerASCII
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.perennial.goose.model.strings (wp_string_len)

namespace net.http

theorem sintZ_len' (n : Nat) (h : n < 2 ^ 63) : sint.Z (W64 (n : Int)) = n := by word

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.http.Assumptions]

theorem modelTokenEqual.wp_proof (wp_lower : modelLowerASCII.spec (GF := GF) (hG := hG)) :
    modelTokenEqual.spec (GF := GF) (hG := hG) := by
  intro t1 t2
  wp_start
  wp_auto
  wp_apply wp_string_len as %H1
  wp_apply wp_string_len as %H2
  wp_if_destruct
  rotate_left
  · iapply HΦ; itrivial
  have hlen : t1.length = t2.length := by
    have := congrArg sint.Z Hif
    rw [sintZ_len' _ H1, sintZ_len' _ H2] at this; omega
  ihave HI : (∃ (i : w64), "i" ∷ i_ptr ↦ i ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.nat i ≤ t1.length⌝ : IProp GF) $$ [i]
  · iexists W64 0
    iframe
    ipureintro
    exact ⟨by word, by word⟩
  wp_for HI
  wp_apply wp_string_len as %-
  have hl1 := sintZ_len' _ H1
  by_cases hlt : sint.Z i < sint.Z (W64 (t1.length : Int))
  · simp only [hlt, _root_.decide_true, ↓reduceIte]
    have hi1 : sint.nat i < t1.length := by word
    have hi2 : sint.nat i < t2.length := hlen ▸ hi1
    obtain ⟨x1, hx1⟩ : ∃ x, t1[sint.nat i]? = some x := ⟨_, List.getElem?_eq_getElem hi1⟩
    obtain ⟨x2, hx2⟩ : ∃ x, t2[sint.nat i]? = some x := ⟨_, List.getElem?_eq_getElem hi2⟩
    wp_auto
    rw [ite_eq_left_of_eq_true _ _ (eq_true Hi.1), hx1]
    wp_auto
    all_goals repeat (first | wp_if_destruct | wp_for_post | wp_apply wp_lower | wp_auto |
      (rw [ite_eq_left_of_eq_true _ _ (eq_true Hi.1), hx2]))
    · iapply HΦ; itrivial
    wp_apply (wp_lower x1)
    rw [ite_eq_left_of_eq_true _ _ (eq_true Hi.1), hx2]
    wp_auto
    wp_apply (wp_lower x2)
    all_goals repeat (first | wp_if_destruct | wp_for_post | wp_auto)
    · iframe
      iexists _
      iframe
      ipureintro
      have hn : sint.nat (i + W64 1) = sint.nat i + 1 := by word
      rw [hn]
      exact ⟨by word, hi1⟩
    · wp_for_post
      iapply HΦ; itrivial
  · simp only [hlt, decide_false, false_neq_true, _root_.decide_true,
      Bool.false_eq_true, ↓reduceIte]
    wp_auto
    iapply HΦ; itrivial

end proof

end net.http
end Perennial
