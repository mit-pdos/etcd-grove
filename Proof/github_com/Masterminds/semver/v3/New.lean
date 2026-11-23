/-
Proof of `Spec/github_com/Masterminds/semver/v3/New.lean` over the real code (`version.go:310-324`;
prove-smalllibs, 2026-11-20: until then a trust-boundary axiom), over `String`'s spec.
-/
module

public import Spec.github_com.Masterminds.semver.v3.New
public import Spec.github_com.Masterminds.semver.v3.Version__String

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

theorem semver.New.wp_proof (hString : semver.Version.String.spec (GF := GF) (hG := hG)) :
    semver.New.spec (GF := GF) (hG := hG) := by
  intro ma mi pa pre md
  wp_start as -
  iapply wp_fupd
  wp_auto
  icases typedPointsto_not_null_dup _ _ _ $$ v with ⟨v, %Hnn⟩
  wp_apply hString v_ptr (DFrac.own 1) _ $$ [v] as v
  · iframe #; iframe v
  ipersist v
  imodintro
  iapply HΦ
  isplitr
  · ipureintro; exact Hnn
  iexists _
  iexact v

end proof

end EtcdGrove
end Perennial
