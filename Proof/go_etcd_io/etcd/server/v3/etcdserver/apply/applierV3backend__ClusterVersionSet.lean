/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend__ClusterVersionSet
public import Spec.github_com.Masterminds.semver.v3.MustParse
public import Spec.github_com.Masterminds.semver.v3.Version__LessThan
public import Spec.github_com.Masterminds.semver.v3.Version__String
public import Spec.go_uber_org.zap.String
public import Spec.go_uber_org.zap.Logger__Info

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.apply go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]


theorem apply.applierV3backend.ClusterVersionSet.wp_proof
    (hMP : semver.MustParse.spec (GF := GF) (hG := hG))
    (hLT : semver.Version.LessThan.spec (GF := GF) (hG := hG))
    (hVS : semver.Version.String.spec (GF := GF) (hG := hG))
    (hZS : zap.String.spec (GF := GF) (hG := hG))
    (hInfo : zap.Logger.Info.spec (GF := GF) (hG := hG)) :
    apply.applierV3backend.ClusterVersionSet.spec (GF := GF) (hG := hG) := by
  intro E p r v3 log Pre Q Post
  wp_start as ⟨#Hb, ⟨%ver, #Hr, %Hvalid⟩, Hpre⟩
  iunfold apply.mPreV at Hpre
  icases Hpre with ⟨Hkv, Hres, Hcs⟩
  iunfold apply.backendIs at Hb
  icases Hb with ⟨%opts, #Hopts, #Hok⟩
  iunfold apply.backendOptsOk at Hok
  icases Hok with ⟨%Hlg, -, -, -, -, -, #Hc, -, #Hss, -⟩
  iunfold apply.isCluster at Hc
  icases Hc with ⟨%Hcnn, #HVer, -, #HSV, -⟩
  iunfold apply.isSnapshotServer at Hss
  icases Hss with ⟨%si, %Hsi, #HFS⟩
  iunfold apply.clusterVersionSetIs at Hr
  icases Hr with ⟨%Hrnn, #Hver⟩
  iStructNamed Hopts
  wp_auto
  wp_apply HVer as %prev #Hprevv
  wp_apply hMP as %nv ⟨%Hnv, %nver, #Hnver⟩
  · ipureintro; exact Hvalid
  (try wp_auto)
  wp_apply HSV $$ [$Hcs] as HPP
  · ipureintro; exact Hnv
  wp_if_destruct
  · -- no previous version
    iapply HΦ
    iunfold apply.mPostV
    iframe
  wp_apply hLT as %b -
  · ipureintro; exact ⟨Hnv, Hif⟩
  have Hprev : prev ≠ null := Hif
  wp_if_destruct
  · -- not a downgrade
    iapply HΦ
    iunfold apply.mPostV
    iframe
  -- a downgrade: logged, a snapshot forced
  wp_if_destruct
  · exact absurd Hif Hlg
  icases Hprevv with (%Hpn | ⟨%pver, #Hpver⟩)
  · exact absurd Hpn Hprev
  (try wp_auto)
  wp_apply hVS as %s1 -
  wp_apply hZS as %f1 -
  (try wp_auto)
  wp_apply hVS as %s2 -
  wp_apply hZS as %f2 -
  wp_apply wp_slice_literal (l := [f1, f2])
  isplitr
  · ipureintro; rfl
  iintro %fsl -
  wp_auto
  wp_apply hInfo
  · ipureintro; exact Hlg
  rw [Hsi]
  wp_apply HFS
  iapply HΦ
  iunfold apply.mPostV
  iframe

end proof

end EtcdGrove
end Perennial
