/-
Proof of `Spec/github_com/Masterminds/semver/v3/Version__Compare.lean` over the real code
(prove-ps2-semver, 2026-11-22), over the specs of `Major`, `Minor`, `Patch`, `Prerelease`,
`compareSegment` and `comparePrerelease`.
-/
module

public import Spec.github_com.Masterminds.semver.v3.Version__Compare
public import Spec.github_com.Masterminds.semver.v3.Version__Major
public import Spec.github_com.Masterminds.semver.v3.Version__Minor
public import Spec.github_com.Masterminds.semver.v3.Version__Patch
public import Spec.github_com.Masterminds.semver.v3.Version__Prerelease
public import Spec.github_com.Masterminds.semver.v3.compareSegment
public import Spec.github_com.Masterminds.semver.v3.comparePrerelease

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.Masterminds.semver.v3.Assumptions]

set_option linter.unusedSimpArgs false in
theorem semver.Version.Compare.wp_proof
    (wp_Major : semver.Version.Major.spec (GF := GF) (hG := hG))
    (wp_Minor : semver.Version.Minor.spec (GF := GF) (hG := hG))
    (wp_Patch : semver.Version.Patch.spec (GF := GF) (hG := hG))
    (wp_Prerelease : semver.Version.Prerelease.spec (GF := GF) (hG := hG))
    (wp_compareSegment : semver.compareSegment.spec (GF := GF) (hG := hG))
    (wp_comparePrerelease : semver.comparePrerelease.spec (GF := GF) (hG := hG)) :
    semver.Version.Compare.spec (GF := GF) (hG := hG) := by
  intro v o dv dw x y
  wp_start as ⟨Hv, Ho⟩
  wp_auto
  wp_apply wp_Major v dv x $$ [Hv] as Hv
  · iframe
  wp_apply wp_Major o dw y $$ [Ho] as Ho
  · iframe
  wp_apply wp_compareSegment
  unfold semver.compare
  wp_if_destruct
  rotate_left
  · rw [ite_eq_left (by simpa using Hif)]
    iapply HΦ; iframe
  rw [ite_eq_right (by simpa using Hif)]
  wp_apply wp_Minor v dv x $$ [Hv] as Hv
  · iframe
  wp_apply wp_Minor o dw y $$ [Ho] as Ho
  · iframe
  wp_apply wp_compareSegment
  wp_if_destruct
  rotate_left
  · rw [ite_eq_left (by simpa using Hif)]
    iapply HΦ; iframe
  rw [ite_eq_right (by simpa using Hif)]
  wp_apply wp_Patch v dv x $$ [Hv] as Hv
  · iframe
  wp_apply wp_Patch o dw y $$ [Ho] as Ho
  · iframe
  wp_apply wp_compareSegment
  wp_if_destruct
  rotate_left
  · rw [ite_eq_left (by simpa using Hif)]
    iapply HΦ; iframe
  rw [ite_eq_right (by simpa using Hif)]
  ihave %Hvnn := typedPointsto_not_null _ _ _ $$ Hv
  iStructNamed Hv
  wp_auto
  ihave Hv : v ↦{dv} x $$ [major minor patch pre metadata original]
  · iapply typedPointsto_combine _ _ _ Hvnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  wp_apply wp_Prerelease o dw y $$ [Ho] as Ho
  · iframe
  by_cases hx : x.pre' = [] <;> by_cases hy : y.pre' = [] <;>
    simp only [hx, hy, decide_true, decide_false, and_self, and_true, true_and, and_false,
      false_and, ↓reduceIte] <;> wp_auto
  · iapply HΦ; iframe
  · rw [decide_eq_false hy]; wp_auto
    iapply HΦ; iframe
  · rw [decide_eq_false hx]; wp_auto
    iapply HΦ; iframe
  · rw [decide_eq_false hx]; wp_auto; rw [decide_eq_false hy]; wp_auto
    wp_apply wp_comparePrerelease
    iapply HΦ; iframe

end proof

end EtcdGrove
end Perennial
