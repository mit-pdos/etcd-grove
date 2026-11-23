/-
The proof of `version.LessThan` (`api/v3/version`: `ver1.LessThan(&ver2)`, the arguments passed
by value, so both receivers are fresh allocations, not nil), over `semver.Version.LessThan`'s
spec (until 2026-11-19 a trust-boundary axiom). Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.api.v3.version.LessThan
public import Spec.github_com.Masterminds.semver.v3.Version__LessThan

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
variable [package_sem : go_etcd_io.etcd.api.v3.version.Assumptions]

theorem version.LessThan.wp_proof
    (wp_LessThan : semver.Version.LessThan.spec (GF := GF) (hG := hG)) :
    version.LessThan.spec (GF := GF) (hG := hG) := by
  intro a b
  wp_start as #Hpkg
  ihave #Hsv : isPkgInit (PROP := IProp GF) pkg_id.github_com.Masterminds.semver.v3 $$ []
  · iPkgInit
  wp_auto
  ihave %h1 := typedPointsto_not_null _ _ _ $$ ver1
  ihave %h2 := typedPointsto_not_null _ _ _ $$ ver2
  wp_apply wp_LessThan
  · ipureintro; exact ⟨h1, h2⟩
  iintro %r -
  wp_auto
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
