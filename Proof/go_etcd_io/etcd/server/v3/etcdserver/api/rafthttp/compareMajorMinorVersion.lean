/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/compareMajorMinorVersion.lean`. Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.compareMajorMinorVersion
public import Spec.github_com.Masterminds.semver.v3.New
public import Spec.github_com.Masterminds.semver.v3.Version__Major
public import Spec.github_com.Masterminds.semver.v3.Version__Minor

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Assumptions]

theorem rafthttp.compareMajorMinorVersion.wp_proof
    (hNew : semver.New.spec (GF := GF) (hG := hG))
    (hMajor : semver.Version.Major.spec (GF := GF) (hG := hG))
    (hMinor : semver.Version.Minor.spec (GF := GF) (hG := hG))
    (hLT : semver.Version.LessThan.spec (GF := GF) (hG := hG)) :
    rafthttp.compareMajorMinorVersion.spec (GF := GF) (hG := hG) := by
  intro a b Ha Hb
  wp_start as -
  ihave #Hsp : isPkgInit (PROP := IProp GF) pkg_id.github_com.Masterminds.semver.v3 $$ []
  · iPkgInit
  wp_auto
  wp_apply hMajor a $$ [] as %ma -
  · iframe #; ipureintro; exact Ha
  wp_apply hMinor a $$ [] as %mi -
  · iframe #; ipureintro; exact Ha
  wp_apply hNew as %na %Hna
  (try wp_auto)
  wp_apply hMajor b $$ [] as %mb -
  · iframe #; ipureintro; exact Hb
  wp_apply hMinor b $$ [] as %mib -
  · iframe #; ipureintro; exact Hb
  wp_apply hNew as %nb %Hnb
  (try wp_auto)
  wp_apply hLT na nb $$ [] as %b1 -
  · iframe #; ipureintro; exact ⟨Hna, Hnb⟩
  (try wp_auto)
  cases b1
  · (try wp_auto)
    wp_apply hLT nb na $$ [] as %b2 -
    · iframe #; ipureintro; exact ⟨Hnb, Hna⟩
    (try wp_auto)
    cases b2 <;> (try wp_auto) <;> (iapply HΦ; itrivial)
  · (try wp_auto)
    iapply HΦ; itrivial

end proof

end EtcdGrove
end Perennial
