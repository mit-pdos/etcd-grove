/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__downgradeEnable.lean`. Lean-first
(the downgrade API, etcd-io/etcd#22575, 2026-10-16).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__downgradeEnable
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Logger
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.convertToClusterVersion
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.version.Manager__DowngradeEnable
public import Spec.github_com.Masterminds.semver.v3.Version__String
public import Spec.go_etcd_io.etcd.api.v3.version.Cluster
public import Spec.go_uber_org.zap.Error
public import Spec.go_uber_org.zap.Logger__Warn

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

set_option hygiene false in
/-- A rejected request: the warning, then `nil` and the error. -/
local macro "dge_reject" : tactic => `(tactic| (
  (try wp_auto)
  wp_apply hErr $$ [] as %f -
  (try wp_auto)
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %fsl ⟨-, -⟩
  (try wp_auto)
  wp_apply hWarn l _ _ $$ []
  · iframe #; ipureintro; exact Hlnn
  (try wp_auto)
  iapply HΦ
  iframe Hrd
  iunfold dgOutcome
  iright; ileft
  simp only [ite_true]
  iframe Hlb
  ipureintro
  simp))

theorem EtcdServer.downgradeEnable.wp_proof
    (hLg : EtcdServer.Logger.spec (GF := GF) (hG := hG))
    (hConv : convertToClusterVersion.spec (GF := GF) (hG := hG))
    (hDE : version.Manager.DowngradeEnable.spec (GF := GF) (hG := hG))
    (hErr : zap.Error.spec (GF := GF) (hG := hG))
    (hWarn : zap.Logger.Warn.spec (GF := GF) (hG := hG))
    (hStr : semver.Version.String.spec (GF := GF) (hG := hG))
    (hCl : version.Cluster.spec (GF := GF) (hG := hG)) :
    EtcdServer.downgradeEnable.spec (GF := GF) (hG := hG) := by
  intro s l γcv known ctx r act ver
  wp_start as ⟨#Hcv, #Hver, #Herr, #Hverr, Hk, #Hlg, %Hlnn, Hrd, #Hr⟩
  ihave #Psv : isPkgInit (PROP := IProp GF) pkg_id.github_com.Masterminds.semver.v3 $$ []
  · iPkgInit
  ihave #Pzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave #Pav : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.version $$ []
  · iPkgInit
  ihave #Pdv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.version $$ []
  · iPkgInit
  iunfold srvDgErrVars at Herr
  icases Herr with ⟨#Hcvu, #Hum, #Hwf⟩
  iunfold dgErrVar at Hcvu
  icases Hcvu with ⟨%ecvu, #Hecvu⟩
  iunfold dgRequestIs at Hr
  icases Hr with ⟨-, #Hrv⟩
  iunfold clusterVersionAt at Hcv
  iunfold srvVersionOk at Hver
  wp_auto
  wp_apply hLg s l $$ [Hrd] as ⟨-, Hrd⟩
  · iframe #; iframe Hrd; ipureintro; exact Hlnn
  (try wp_auto)
  wp_apply Hcv $$ %known [Hk] as %cv Hcvr
  · iexact Hk
  (try wp_auto)
  wp_if_destruct
  · -- the version is not known yet: the PR's guard
    icases Hcvr with (%Hc | ⟨%Hcnn, -⟩)
    rotate_left
    · exact absurd rfl Hcnn
    have Hkf : known = false := Hc.2
    (try wp_auto)
    iapply HΦ
    iframe Hrd
    iunfold dgOutcome
    ileft
    isplitr
    · ipureintro; exact ⟨rfl, Hkf⟩
    iunfold dgErrIs
    iexists ecvu; iframe Hecvu; ipureintro; rfl
  · icases Hcvr with (%Hc | ⟨%Hcnn, #Hlb⟩)
    · exact absurd Hc.1 (by assumption)
    (try wp_auto)
    wp_apply hConv ver $$ [] as %tv %err Htv
    · iframe #; iunfold srvDgErrVars; iframe #; iunfold dgErrVar; iexists ecvu; iexact Hecvu
    (try wp_auto)
    icases Htv with (%Htv | ⟨%Htv, #Hwfe⟩)
    · obtain ⟨rfl, Htvnn⟩ := Htv
      (try wp_auto)
      wp_apply Hver $$ [] as %m ⟨%si, #Hm, #Hsi⟩
      (try wp_auto)
      wp_apply hDE m si γcv ctx tv $$ [] as %err' -
      · iframe #; ipureintro; exact Htvnn
      (try wp_auto)
      rcases err' with ei | _
      · dge_reject
      · (try wp_auto)
        wp_apply hStr cv $$ [] as %str -
        · iframe #; ipureintro; exact Hcnn
        (try wp_auto)
        wp_apply hCl $$ [] as %cs -
        (try wp_auto)
        iapply HΦ
        iframe Hrd
        iunfold dgOutcome
        iright; iright
        icases typedPointsto_not_null_dup _ _ _ $$ resp with ⟨Hr', %Hrnn⟩
        isplitr
        · ipureintro; exact ⟨rfl, Hrnn⟩
        iframe Hlb
        iunfold dgResp; iexists _; iexact Hr'
    · subst Htv
      iunfold dgErrIs at Hwfe
      icases Hwfe with ⟨%e, #He, %Hee⟩
      subst Hee
      dge_reject

end proof

end EtcdGrove
end Perennial
