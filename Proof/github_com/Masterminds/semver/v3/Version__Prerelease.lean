/-
Proof of `Spec/github_com/Masterminds/semver/v3/Version__Prerelease.lean` over the real code
(prove-ps2-semver, 2026-11-22).
-/
module

public import Spec.github_com.Masterminds.semver.v3.Version__Prerelease

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

theorem semver.Version.Prerelease.wp_proof : semver.Version.Prerelease.spec (GF := GF) (hG := hG) := by
  intro v dq x
  wp_start as Hv
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  iapply HΦ $$ Hv

end proof

end EtcdGrove
end Perennial
