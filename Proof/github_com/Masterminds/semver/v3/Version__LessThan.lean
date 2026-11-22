/-
Proof of `Spec/github_com/Masterminds/semver/v3/Version__LessThan.lean` over the real code
(`version.go:486-488`; prove-ps2-semver, 2026-11-22: until then a trust-boundary axiom, of any
receivers not nil, returning some boolean), over `Compare`'s spec.
-/
module

public import Spec.github_com.Masterminds.semver.v3.Version__LessThan
public import Spec.github_com.Masterminds.semver.v3.Version__Compare

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

theorem semver.Version.LessThan.wp_proof
    (wp_Compare : semver.Version.Compare.spec (GF := GF) (hG := hG)) :
    semver.Version.LessThan.spec (GF := GF) (hG := hG) := by
  intro v o dv dw x y
  wp_start as ⟨Hv, Ho⟩
  wp_auto
  wp_apply wp_Compare v o dv dw x y $$ [Hv Ho] as ⟨Hv, Ho⟩
  · iframe
  have hlt : decide (sint.Z (semver.compare x y) < sint.Z (W64 0)) = decide (semver.lessThan x y) := by
    unfold semver.lessThan; simp
  rw [hlt]
  iapply HΦ
  iframe

end proof

end EtcdGrove
end Perennial
