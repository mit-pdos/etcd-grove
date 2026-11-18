/-
`version.LessThan(ver1, ver2)` (`version.go`: `ver1.LessThan(&ver2)`), verified: translated with
its body (`Code/go_etcd_io/etcd/api/v3/version.toml`), over semver's `Version.LessThan` spec.
Until 2026-11-18 a trust-boundary axiom.
-/
module

public import Spec.go_etcd_io.etcd.api.v3.version.LessThan
public import Spec.github_com.Masterminds.semver.v3.Version__LessThan

@[expose] public section

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
  wp_start
  wp_auto
  icases typedPointsto_not_null_dup _ _ _ $$ ver1 with ⟨ver1, %H1⟩
  icases typedPointsto_not_null_dup _ _ _ $$ ver2 with ⟨ver2, %H2⟩
  wp_apply wp_LessThan as %r -
  · ipureintro; exact ⟨H1, H2⟩
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
