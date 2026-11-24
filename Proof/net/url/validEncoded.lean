/-
The proof of `validEncoded.spec` (`Spec/net/url/validEncoded.lean`).
-/
module

public import Spec.net.url.validEncoded
public import Spec.net.url.shouldEscape
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.perennial.goose.model.strings (wp_string_len)

namespace net.url

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : net.url.Assumptions]

/-- The bytes `validEncoded` accepts whatever the mode. -/
private abbrev veList : List w8 :=
  [W8 33, W8 36, W8 38, W8 39, W8 40, W8 41, W8 42, W8 43, W8 44, W8 59, W8 61, W8 58, W8 64,
    W8 91, W8 93, W8 37]

private theorem all_take_succ (s : List w8) (p : w8 → Bool) (i : Nat) (x : w8) (hx : s[i]? = some x) :
    (s.take (i + 1)).all p = ((s.take i).all p && p x) := by
  rw [List.take_add_one, hx]; simp [List.all_append]

theorem validEncoded.wp_proof (wp_shouldEscape : shouldEscape.spec (GF := GF) (hG := hG)) :
    validEncoded.spec (GF := GF) (hG := hG) := by
  intro s mode hmode
  wp_start
  wp_auto
  ihave HI : (∃ (i : w64), "i" ∷ i_ptr ↦ i ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.nat i ≤ s.length ∧
        (s.take (sint.nat i)).all (fun c => veList.contains c || !shouldEscapeRef c mode) = true⌝ :
      IProp GF) $$ [i]
  · iexists W64 0
    iframe
    ipureintro
    refine ⟨by word, by word, ?_⟩
    rw [show sint.nat (W64 0) = 0 from rfl]; simp
  wp_for HI
  wp_apply wp_string_len as %Hl
  by_cases hlt : sint.Z i < sint.Z (W64 (s.length : Int))
  · simp only [hlt, _root_.decide_true, ↓reduceIte]
    have hi : sint.nat i < s.length := by word
    obtain ⟨x, hx⟩ : ∃ x, s[sint.nat i]? = some x := ⟨_, List.getElem?_eq_getElem hi⟩
    wp_auto
    rw [ite_eq_left_of_eq_true _ _ (eq_true Hi.1), hx]
    wp_auto
    by_cases hin : veList.contains x = true
    · have hstep : (s.take (sint.nat (i + W64 1))).all
          (fun c => veList.contains c || !shouldEscapeRef c mode) = true := by
        have hn : sint.nat (i + W64 1) = sint.nat i + 1 := by word
        rw [hn, all_take_succ s _ _ x hx, Hi.2.2, hin]; rfl
      have hmem : x ∈ veList := by simpa using hin
      simp only [veList, List.mem_cons, List.not_mem_nil, _root_.or_false] at hmem
      rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl <;>
      · wp_auto
        wp_for_post
        iframe
        iexists _
        iframe
        ipureintro
        exact ⟨by word, by word, hstep⟩
    · have d33 : decide (x = W8 33) = false := by
        rw [decide_eq_false_iff_not]; rintro rfl; exact hin (by decide)
      have d36 : decide (x = W8 36) = false := by
        rw [decide_eq_false_iff_not]; rintro rfl; exact hin (by decide)
      have d38 : decide (x = W8 38) = false := by
        rw [decide_eq_false_iff_not]; rintro rfl; exact hin (by decide)
      have d39 : decide (x = W8 39) = false := by
        rw [decide_eq_false_iff_not]; rintro rfl; exact hin (by decide)
      have d40 : decide (x = W8 40) = false := by
        rw [decide_eq_false_iff_not]; rintro rfl; exact hin (by decide)
      have d41 : decide (x = W8 41) = false := by
        rw [decide_eq_false_iff_not]; rintro rfl; exact hin (by decide)
      have d42 : decide (x = W8 42) = false := by
        rw [decide_eq_false_iff_not]; rintro rfl; exact hin (by decide)
      have d43 : decide (x = W8 43) = false := by
        rw [decide_eq_false_iff_not]; rintro rfl; exact hin (by decide)
      have d44 : decide (x = W8 44) = false := by
        rw [decide_eq_false_iff_not]; rintro rfl; exact hin (by decide)
      have d59 : decide (x = W8 59) = false := by
        rw [decide_eq_false_iff_not]; rintro rfl; exact hin (by decide)
      have d61 : decide (x = W8 61) = false := by
        rw [decide_eq_false_iff_not]; rintro rfl; exact hin (by decide)
      have d58 : decide (x = W8 58) = false := by
        rw [decide_eq_false_iff_not]; rintro rfl; exact hin (by decide)
      have d64 : decide (x = W8 64) = false := by
        rw [decide_eq_false_iff_not]; rintro rfl; exact hin (by decide)
      have d91 : decide (x = W8 91) = false := by
        rw [decide_eq_false_iff_not]; rintro rfl; exact hin (by decide)
      have d93 : decide (x = W8 93) = false := by
        rw [decide_eq_false_iff_not]; rintro rfl; exact hin (by decide)
      have d37 : decide (x = W8 37) = false := by
        rw [decide_eq_false_iff_not]; rintro rfl; exact hin (by decide)
      iterate 17 ((try simp only [d33, d36, d38, d39, d40, d41, d42, d43, d44, d59, d61, d58, d64, d91, d93, d37]); (try wp_auto))
      rw [ite_eq_left_of_eq_true _ _ (eq_true Hi.1), hx]
      wp_auto
      wp_apply wp_shouldEscape
      rw [encTable_mode x mode hmode]
      cases hse : shouldEscapeRef x mode
      · wp_auto
        wp_for_post
        iframe
        iexists _
        iframe
        ipureintro
        have hn : sint.nat (i + W64 1) = sint.nat i + 1 := by word
        refine ⟨by word, by omega, ?_⟩
        rw [hn, all_take_succ s _ _ x hx, Hi.2.2, hse]; simp
      · wp_auto
        wp_for_post
        have : validEncodedF s mode = false := by
          unfold validEncodedF
          rw [List.all_eq_false]
          refine ⟨x, List.mem_of_getElem? hx, ?_⟩
          rw [hse]; simpa using hin
        rw [this]
        iapply HΦ; itrivial
  · simp only [hlt, decide_false, false_neq_true, _root_.decide_true, Bool.false_eq_true, ↓reduceIte]
    wp_auto
    have hi : sint.nat i = s.length := by word
    have := Hi.2.2
    rw [hi, List.take_length] at this
    unfold validEncodedF
    rw [this]
    iapply HΦ; itrivial

end proof

end net.url
end Perennial
