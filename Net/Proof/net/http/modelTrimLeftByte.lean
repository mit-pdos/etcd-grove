/-
The proof of `modelTrimLeftByte` (`Net/Spec/net/http/modelTrimLeftByte.lean`): the loop drops the
leading `c`s one at a time.
-/
module

public import Net.Spec.net.http.modelTrimLeftByte
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.perennial.goose.model.strings (wp_string_len)

namespace net.http

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.http.Assumptions]

theorem modelTrimLeftByte.wp_proof : modelTrimLeftByte.spec (GF := GF) (hG := hG) := by
  intro s c
  wp_start
  wp_auto
  ihave HI : (∃ (s' : GoString), "s" ∷ s_ptr ↦ s' ∗
      "%Hs" ∷ ⌜trimLeftByte s' c = trimLeftByte s c⌝ : IProp GF) $$ [s]
  · iexists s
    iframe
    ipureintro; rfl
  wp_for HI
  wp_apply wp_string_len as %Hl
  rcases s' with _ | ⟨x, t⟩
  · rw [decide_eq_false (by simp)]
    wp_auto
    wp_if_destruct
    · exact absurd Hif false_neq_true
    · rw [show trimLeftByte s c = [] from Hs.symm]
      iapply HΦ; itrivial
  · rw [decide_eq_true (by simp only [List.length_cons] at Hl ⊢; word)]
    wp_auto
    wp_if_destruct
    · have hx : x = c := Decidable.byContradiction fun h =>
        false_neq_true (by rw [decide_eq_false h] at Hif; exact Hif)
      wp_apply wp_string_len as %Hl'
      have Hl2 : t.length + 1 < 2 ^ 63 := by simpa using Hl
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by simp only [List.length_cons]; word,
        by simp only [List.length_cons]; word⟩)]
      wp_auto
      wp_for_post
      iframe
      iexists _
      iframe
      ipureintro
      have hn : sint.nat (W64 ((t.length : Int) + 1)) = t.length + 1 := by word
      rw [← Hs]
      simp [trimLeftByte, List.dropWhile, hx, hn]
    · have hx : x ≠ c := fun h => Hif (by rw [decide_eq_true h])
      rw [decide_eq_false hx]
      simp only [Bool.false_eq_true, ↓reduceIte]
      wp_auto
      have : trimLeftByte s c = x :: t := by
        rw [← Hs]; simp [trimLeftByte, List.dropWhile, hx]
      rw [this]
      iapply HΦ; itrivial

end proof

end net.http
end Perennial
