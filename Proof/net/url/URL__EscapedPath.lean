/-
The proof of `URL.EscapedPath.spec` (`Spec/net/url/URL__EscapedPath.lean`).
-/
module

public import Spec.net.url.URL__EscapedPath
public import Spec.net.url.unescape
public import Spec.net.url.escape
public import Spec.net.url.validEncoded

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace net.url

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : net.url.Assumptions]

set_option hygiene false in
/-- The end of `EscapedPath`, once its result is `"*"` or `escape(u.Path)`. -/
local macro "escapedPath_tail" : tactic => `(tactic| (
  wp_if_destruct
  · rw [ite_eq_left (show v.Path' = [42#8] from Hif)]
    iapply HΦ
    iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  · wp_apply wp_escape v.Path' mPath (by decide)
    rw [ite_eq_right (show ¬ v.Path' = [42#8] from Hif)]
    iapply HΦ
    iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe))

theorem URL.EscapedPath.wp_proof (wp_unescape : unescape.spec (GF := GF) (hG := hG))
    (wp_escape : escape.spec (GF := GF) (hG := hG))
    (wp_validEncoded : validEncoded.spec (GF := GF) (hG := hG)) :
    URL.EscapedPath.spec (GF := GF) (hG := hG) := by
  intro u dq v
  wp_start as Hu
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hu
  iStructNamed Hu
  wp_auto
  wp_if_destruct
  · have hE : escapedPathF v.RawPath' v.Path' =
        (if v.Path' = [42#8] then [42#8] else escapeF v.Path' mPath) := by
      simp [escapedPathF, Hif]
    rw [hE]
    escapedPath_tail
  · wp_apply wp_validEncoded v.RawPath' mPath (by decide)
    cases hv : validEncodedF v.RawPath' mPath
    · have hE : escapedPathF v.RawPath' v.Path' =
          (if v.Path' = [42#8] then [42#8] else escapeF v.Path' mPath) := by
        unfold escapedPathF; simp only [hv, Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte, beq_iff_eq]; rfl
      rw [hE]
      wp_auto
      escapedPath_tail
    · wp_auto
      wp_apply wp_unescape v.RawPath' mPath (by decide)
      cases hu : unescapeF v.RawPath' mPath with
      | error e =>
        have hE : escapedPathF v.RawPath' v.Path' =
            (if v.Path' = [42#8] then [42#8] else escapeF v.Path' mPath) := by
          unfold escapedPathF; simp only [hu, Bool.and_false, Bool.false_eq_true,
            ↓reduceIte, beq_iff_eq]; rfl
        rw [hE]
        simp only [unescRes, hu]
        cases e <;> (simp only [unescErrV, interface.mkOk]; wp_auto; escapedPath_tail)
      | ok q =>
        simp only [unescRes, hu]
        wp_auto
        wp_if_destruct
        · have hE : escapedPathF v.RawPath' v.Path' = v.RawPath' := by
            unfold escapedPathF; rw [hu, hv]; simp [Hif]
          rw [hE]
          iapply HΦ
          iapply typedPointsto_combine _ _ _ Hnn
          simp only [TypedPointsto.typedPointstoDef]
          iframe
        · have hE : escapedPathF v.RawPath' v.Path' =
              (if v.Path' = [42#8] then [42#8] else escapeF v.Path' mPath) := by
            unfold escapedPathF; rw [hu, hv]; simp [Hif]
          rw [hE]
          escapedPath_tail

end proof

end net.url
end Perennial
