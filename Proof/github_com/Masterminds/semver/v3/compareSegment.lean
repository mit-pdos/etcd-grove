/-
Proof of `Spec/github_com/Masterminds/semver/v3/compareSegment.lean` over the real code
(prove-ps2-semver, 2026-11-22).
-/
module

public import Spec.github_com.Masterminds.semver.v3.compareSegment

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

theorem semver.compareSegment.wp_proof : semver.compareSegment.spec (GF := GF) (hG := hG) := by
  intro v o
  wp_start as -
  wp_auto
  unfold semver.cmpSeg
  wp_if_destruct
  · rw [ite_eq_left (by word)]
    iapply HΦ; itrivial
  wp_if_destruct
  · rw [ite_eq_right (by word), ite_eq_left (by word)]
    iapply HΦ; itrivial
  rw [ite_eq_right (by word), ite_eq_right (by word)]
  iapply HΦ; itrivial

end proof

end EtcdGrove
end Perennial
