/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/version/allowedDowngradeVersion.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.version.allowedDowngradeVersion
public import Spec.github_com.Masterminds.semver.v3.Version__Major
public import Spec.github_com.Masterminds.semver.v3.Version__Minor
public import Spec.github_com.Masterminds.semver.v3.New

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.version

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.version.Assumptions]

theorem version.allowedDowngradeVersion.wp_proof
    (hMaj : semver.Version.Major.spec (GF := GF) (hG := hG))
    (hMin : semver.Version.Minor.spec (GF := GF) (hG := hG))
    (hNew : semver.New.spec (GF := GF) (hG := hG)) :
    version.allowedDowngradeVersion.spec (GF := GF) (hG := hG) := by
  intro ver
  wp_start as %Hver
  ihave #Psv : isPkgInit (PROP := IProp GF) pkg_id.github_com.Masterminds.semver.v3 $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply hMaj ver $$ [] as %maj -
  · iframe #; ipureintro; exact Hver
  (try wp_auto)
  wp_apply hMin ver $$ [] as %mi -
  · iframe #; ipureintro; exact Hver
  (try wp_auto)
  wp_apply hNew as %v %Hv
  iapply HΦ
  ipureintro; exact Hv

end proof

end EtcdGrove
end Perennial
