/-
Proof of `Spec/github_com/Masterminds/semver/v3/Version__Major.lean` over the real code (`version.go:360-363`;
prove-smalllibs, 2026-11-20: until then a trust-boundary axiom).
-/
module

public import Spec.github_com.Masterminds.semver.v3.Version__Major

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

theorem semver.Version.Major.wp_proof : semver.Version.Major.spec (GF := GF) (hG := hG) := by
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
