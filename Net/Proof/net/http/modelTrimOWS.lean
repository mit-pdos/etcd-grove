/-
The proof of `modelTrimOWS` (`Net/Spec/net/http/modelTrimOWS.lean`): the first loop drops the leading
spaces and tabs one at a time, the second the trailing ones.
-/
module

public import Net.Spec.net.http.modelTrimOWS
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.perennial.goose.model.strings (wp_string_len)

namespace net.http

/-- `trimOWS` once the leading spaces are gone: the trailing ones dropped. -/
def trimOWSR (y : List w8) : List w8 := (y.reverse.dropWhile isOWS).reverse

theorem trimOWS_cons (a : w8) (t : List w8) (h : isOWS a = true) :
    trimOWS (a :: t) = trimOWS t := by
  simp [trimOWS, h]

theorem trimOWS_eq_R (y : List w8) (h : ∀ a t, y = a :: t → isOWS a = false) :
    trimOWS y = trimOWSR y := by
  cases y with
  | nil => rfl
  | cons a t => simp [trimOWS, trimOWSR, h a t rfl]

theorem trimOWSR_dropLast (y : List w8) (hy : y ≠ []) (h : isOWS (y.getLast hy) = true) :
    trimOWSR y = trimOWSR y.dropLast := by
  conv => lhs; rw [← List.dropLast_concat_getLast hy]
  simp [trimOWSR, List.reverse_append, h]

theorem trimOWSR_id (y : List w8) (h : ∀ hy : y ≠ [], isOWS (y.getLast hy) = false) :
    trimOWSR y = y := by
  by_cases hy : y = []
  · subst hy; rfl
  · have h1 := h hy
    conv => lhs; rw [← List.dropLast_concat_getLast hy]
    simp [trimOWSR, List.reverse_append, h1]
    exact List.dropLast_concat_getLast hy

set_option hygiene false in
/-- The second loop, from `x ↦ L` with `HR : trimOWSR L = trimOWS x0`. -/
local macro "trim_loop2" : tactic => `(tactic| (
  ihave HI2 : (∃ (y : GoString), "x" ∷ x_ptr ↦ y ∗
      "%Hy" ∷ ⌜trimOWSR y = trimOWS x0⌝ : IProp GF) $$ [x]
  · iexists _
    iframe
    ipureintro; exact HR
  wp_for HI2
  wp_apply wp_string_len as %Hl
  rcases List.eq_nil_or_concat y with rfl | ⟨L, b, rfl⟩
  · rw [decide_eq_false (by simp)]
    wp_auto
    rw [if_neg (by simp [false_neq_true]), if_pos (by simp)]
    wp_auto
    rw [← Hy, show trimOWSR [] = [] from rfl]
    iapply HΦ; itrivial
  · simp only [List.concat_eq_append] at Hy Hl ⊢
    rw [decide_eq_true (by simp only [List.length_append, List.length_singleton] at Hl ⊢; word)]
    wp_auto
    wp_apply (wp_string_len (L ++ [b]) (t := go.string)) as %-
    have hL : L.length + 1 < 2 ^ 63 := by simpa using Hl
    have h0 : 0 ≤ sint.Z (W64 ((L ++ [b]).length : Int) - W64 1) := by
      simp only [List.length_append, List.length_singleton]; word
    have hn : sint.nat (W64 ((L ++ [b]).length : Int) - W64 1) = L.length := by
      simp only [List.length_append, List.length_singleton]; word
    have hb' : (L ++ [b])[L.length]? = some b := by simp
    rw [if_pos h0, hn, hb']
    wp_auto
    by_cases ha : b = W8 32
    · rw [decide_eq_true ha]
      wp_auto
      rw [if_pos (by simp)]
      wp_auto
      wp_apply (wp_string_len (L ++ [b]) (t := go.string)) as %-
      have hsl : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (W64 ((L ++ [b]).length : Int) - W64 1) ∧
          sint.Z (W64 ((L ++ [b]).length : Int) - W64 1) ≤ ((L ++ [b]).length : Int) := by
        simp only [List.length_append, List.length_singleton]; exact ⟨by word, by word, by word⟩
      rw [ite_eq_left_of_eq_true _ _ (eq_true hsl)]
      wp_auto
      wp_for_post
      iframe
      iexists _
      iframe
      ipureintro
      rw [hn, Nat.sub_zero, List.drop_zero, List.take_left' rfl, ← Hy,
        trimOWSR_dropLast (L ++ [b]) (by simp) (by simp [isOWS, ha])]
      simp
    · rw [decide_eq_false ha]
      wp_auto
      wp_apply (wp_string_len (L ++ [b]) (t := go.string)) as %-
      rw [if_pos h0, hn, hb']
      wp_auto
      by_cases hb2 : b = W8 9
      · rw [decide_eq_true hb2, if_pos (by simp)]
        wp_auto
        wp_apply (wp_string_len (L ++ [b]) (t := go.string)) as %-
        have hsl : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (W64 ((L ++ [b]).length : Int) - W64 1) ∧
            sint.Z (W64 ((L ++ [b]).length : Int) - W64 1) ≤ ((L ++ [b]).length : Int) := by
          simp only [List.length_append, List.length_singleton]; exact ⟨by word, by word, by word⟩
        rw [ite_eq_left_of_eq_true _ _ (eq_true hsl)]
        wp_auto
        wp_for_post
        iframe
        iexists _
        iframe
        ipureintro
        rw [hn, Nat.sub_zero, List.drop_zero, List.take_left' rfl, ← Hy,
          trimOWSR_dropLast (L ++ [b]) (by simp) (by simp [isOWS, hb2])]
        simp
      · rw [decide_eq_false hb2, if_neg (by simp [false_neq_true]), if_pos (by simp)]
        wp_auto
        rw [← Hy, trimOWSR_id (L ++ [b]) (fun _ => by simp [isOWS]; exact ⟨ha, hb2⟩)]
        iapply HΦ; itrivial))

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.http.Assumptions]

theorem modelTrimOWS.wp_proof : modelTrimOWS.spec (GF := GF) (hG := hG) := by
  intro x0
  wp_start
  wp_auto
  ihave HI : (∃ (x' : GoString), "x" ∷ x_ptr ↦ x' ∗
      "%Hx" ∷ ⌜trimOWS x' = trimOWS x0⌝ : IProp GF) $$ [x]
  · iexists x0
    iframe
    ipureintro; rfl
  wp_for HI
  wp_apply wp_string_len as %Hl
  rcases x' with _ | ⟨y0, t⟩
  · rw [decide_eq_false (by simp)]
    wp_auto
    rw [if_neg (by simp [false_neq_true]), if_pos (by simp)]
    wp_auto
    have HR : trimOWSR [] = trimOWS x0 := Hx
    trim_loop2
  · rw [decide_eq_true (by simp only [List.length_cons] at Hl ⊢; word)]
    wp_auto
    by_cases ha : y0 = W8 32
    · rw [decide_eq_true ha]
      wp_auto
      rw [if_pos (by simp)]
      wp_auto
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
      rw [← Hx, trimOWS_cons y0 t (by simp [isOWS, ha])]
      simp [hn]
    · rw [decide_eq_false ha]
      wp_auto
      by_cases hb : y0 = W8 9
      · rw [decide_eq_true hb]
        rw [if_pos (by simp)]
        wp_auto
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
        rw [← Hx, trimOWS_cons y0 t (by simp [isOWS, hb])]
        simp [hn]
      · rw [decide_eq_false hb]
        rw [if_neg (by simp [false_neq_true]), if_pos (by simp)]
        wp_auto
        have HR : trimOWSR (y0 :: t) = trimOWS x0 := by
          rw [← Hx, trimOWS_eq_R]
          intro c u h; cases h; simp [isOWS]; exact ⟨ha, hb⟩
        trim_loop2

end proof

end net.http
end Perennial
