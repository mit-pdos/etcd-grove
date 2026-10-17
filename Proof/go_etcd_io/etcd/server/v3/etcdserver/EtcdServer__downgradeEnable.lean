/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__downgradeEnable.lean`. Lean-first
(no Rocq counterpart).
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

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem EtcdServer.downgradeEnable.wp_proof
    (hLg : EtcdServer.Logger.spec (GF := GF) (hG := hG))
    (hConv : convertToClusterVersion.spec (GF := GF) (hG := hG))
    (hEnable : version.Manager.DowngradeEnable.spec (GF := GF) (hG := hG))
    (hZE : zap.Error.spec (GF := GF) (hG := hG))
    (hW : zap.Logger.Warn.spec (GF := GF) (hG := hG))
    (hStr : semver.Version.String.spec (GF := GF) (hG := hG))
    (hCl : version.Cluster.spec (GF := GF) (hG := hG)) :
    EtcdServer.downgradeEnable.spec (GF := GF) (hG := hG) := by
  intro s l r ver ctx EP CP
  wp_start as ⟨#Hok, Hrd, #Hver, HEP⟩
  iunfold srvDowngradeOk at Hok
  icases Hok with ⟨%γcv, #Hlg, %Hl, #Hcv, #HVer, #Hf⟩
  iunfold srvClusterVersionAt at Hcv
  ihave #Hf' := Hf
  iunfold version.versionFacts at Hf'
  iunfold dgErrVar at Hf'
  icases Hf' with ⟨-, -, -, ⟨%eC, #HeC⟩⟩
  ihave #Pver : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.version $$ []
  · iPkgInit
  ihave #Psv : isPkgInit (PROP := IProp GF) pkg_id.github_com.Masterminds.semver.v3 $$ []
  · iPkgInit
  ihave #Pav : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.version $$ []
  · iPkgInit
  ihave #Pzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply hLg s l $$ [Hrd] as ⟨-, Hrd⟩
  · iframe #; iframe Hrd; ipureintro; exact Hl
  (try wp_auto)
  wp_apply hConv ver as %tv %err Hconv
  icases Hconv with (%Hc | ⟨%Hc, #Herr⟩)
  · -- converted
    obtain ⟨Hcv1, Htv, rfl⟩ := Hc
    (try wp_auto)
    iunfold srvVersionOk at HVer
    wp_apply HVer $$ [Hrd] as %m ⟨Hrd, %vs, #Hms, #Hsrv⟩
    · iexact Hrd
    (try wp_auto)
    wp_apply hEnable m vs _ _ EP _ ctx tv $$ [HEP] as %err Hout
    · iframe #; iframe HEP; ipureintro; exact Htv
    (try wp_auto)
    cases err with
    | ok ei =>
      (try wp_auto)
      wp_apply hZE as %fld -
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %fs ⟨-, -⟩
      (try wp_auto)
      wp_apply hW l _ _ $$ []
      · iframe #; ipureintro; exact Hl
      (try wp_auto)
      iapply HΦ
      iframe Hrd
      iunfold dgEnablePost
      icases Hout with (⟨-, -, HEP⟩ | -)
      · iright; ileft
        iframe HEP
        ipureintro
        exact ⟨Hcv1, rfl, fun h => by cases h⟩
      · iright; iright; ileft
        ipureintro
        exact ⟨Hcv1, rfl, fun h => by cases h⟩
    | nil =>
      (try wp_auto)
      -- the manager's read saw a non-nil version: the cluster version stays known
      icases Hout with (⟨%Hne, -, -⟩ | ⟨%cv0, %Hcv0, -, Hcvr0⟩)
      · exact absurd rfl Hne
      iunfold srvCVR at Hcvr0
      icases Hcvr0 with (%Hn0 | ⟨-, #Hw⟩)
      · exact absurd Hn0 Hcv0
      wp_apply Hcv $$ %true [] as %cv Hcvr
      · simp; iexact Hw
      icases Hcvr with (%Hc2 | ⟨%Hcvnn, -⟩)
      · exact Hc2.elim
      (try wp_auto)
      wp_if_destruct
      · exact absurd rfl Hcvnn
      · (try wp_auto)
        wp_apply hStr cv $$ [] as %str -
        · iframe #; ipureintro; exact Hcvnn
        (try wp_auto)
        wp_apply hCl as %cs -
        (try wp_auto)
        icases typedPointsto_not_null_dup _ _ _ $$ resp with ⟨resp, %Hrn⟩
        iapply HΦ
        iframe Hrd
        iunfold dgEnablePost
        iright; iright; iright
        iframe resp
        ipureintro
        exact ⟨Hcv1, Hrn, rfl⟩
  · -- not converted: rejected before anything else
    obtain ⟨Hcv1, rfl⟩ := Hc
    ihave %Hne := dgErrIs_ne_nil _ _ $$ Herr
    cases err with
    | nil => exact absurd rfl Hne
    | ok ei =>
      (try wp_auto)
      wp_apply hZE as %fld -
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %fs ⟨-, -⟩
      (try wp_auto)
      wp_apply hW l _ _ $$ []
      · iframe #; ipureintro; exact Hl
      (try wp_auto)
      iapply HΦ
      iframe Hrd
      iunfold dgEnablePost
      ileft
      iframe Herr HEP
      ipureintro
      exact ⟨Hcv1, rfl⟩

end proof

end EtcdGrove
end Perennial
