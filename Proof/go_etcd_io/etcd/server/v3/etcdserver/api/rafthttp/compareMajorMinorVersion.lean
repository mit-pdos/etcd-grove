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
variable [GooseExts] [GooseSemantics] [GooseInterp]
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
  intro a b x y Hann Hbnn
  wp_start as ⟨#Ha, #Hb⟩
  ihave #Hsp : isPkgInit (PROP := IProp GF) pkg_id.github_com.Masterminds.semver.v3 $$ []
  · iPkgInit
  wp_auto
  wp_apply hMajor a DFrac.discard x $$ [] as -
  · iframe #
  wp_apply hMinor a DFrac.discard x $$ [] as -
  · iframe #
  wp_apply hNew as %na ⟨%Hna, %oa, #Hna'⟩
  (try wp_auto)
  wp_apply hMajor b DFrac.discard y $$ [] as -
  · iframe #
  wp_apply hMinor b DFrac.discard y $$ [] as -
  · iframe #
  wp_apply hNew as %nb ⟨%Hnb, %ob, #Hnb'⟩
  (try wp_auto)
  wp_apply hLT na nb DFrac.discard DFrac.discard _ _ $$ [] as -
  · iframe #
  wp_if_destruct
  all_goals try (iapply HΦ; itrivial; done)
  wp_apply hLT nb na DFrac.discard DFrac.discard _ _ $$ [] as -
  · iframe #
  wp_if_destruct
  all_goals (iapply HΦ; itrivial)

end proof

end EtcdGrove
end Perennial
