/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__downgradeCancel.lean`. Lean-first
(no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__downgradeCancel
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.version.Manager__DowngradeCancel
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

theorem EtcdServer.downgradeCancel.wp_proof
    (hCancel : version.Manager.DowngradeCancel.spec (GF := GF) (hG := hG))
    (hZE : zap.Error.spec (GF := GF) (hG := hG))
    (hW : zap.Logger.Warn.spec (GF := GF) (hG := hG))
    (hStr : semver.Version.String.spec (GF := GF) (hG := hG))
    (hCl : version.Cluster.spec (GF := GF) (hG := hG)) :
    EtcdServer.downgradeCancel.spec (GF := GF) (hG := hG) := by
  intro s l ctx EP CP
  wp_start as ⟨#Hok, Hrd, HCP⟩
  iunfold srvDowngradeOk at Hok
  icases Hok with ⟨%γcv, #Hlg, %Hl, #Hcv, #Hver, #Hf⟩
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
  wp_apply Hcv $$ %false [] as %cv Hcvr
  · simp; ipureintro; trivial
  (try wp_auto)
  wp_if_destruct
  · (try wp_auto)
    iapply HΦ
    iframe Hrd
    iunfold dgCancelPost
    ileft
    iframe HCP
    isplitr
    · ipureintro; rfl
    iunfold dgErrIs
    iexists eC
    iframe HeC
    ipureintro; rfl
  · have Hcvnn : cv ≠ null := Hif
    iunfold srvVersionOk at Hver
    wp_apply Hver $$ [Hrd] as %m ⟨Hrd, %vs, #Hms, #Hsrv⟩
    · iexact Hrd
    (try wp_auto)
    wp_apply hCancel m vs _ _ EP CP ctx $$ [HCP] as %err Hout
    · iframe #; iframe HCP
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
      wp_apply hStr cv $$ [] as %str -
      · iframe #; ipureintro; exact Hcvnn
      (try wp_auto)
      wp_apply hCl as %cs -
      (try wp_auto)
      icases typedPointsto_not_null_dup _ _ _ $$ resp with ⟨resp, %Hrn⟩
      iapply HΦ
      iframe Hrd
      iunfold dgCancelPost
      iright
      iframe resp
      ipureintro
      exact ⟨Hrn, rfl⟩
    | nil =>
      (try wp_auto)
      wp_apply hStr cv $$ [] as %str -
      · iframe #; ipureintro; exact Hcvnn
      (try wp_auto)
      wp_apply hCl as %cs -
      (try wp_auto)
      icases typedPointsto_not_null_dup _ _ _ $$ resp with ⟨resp, %Hrn⟩
      iapply HΦ
      iframe Hrd
      iunfold dgCancelPost
      iright
      iframe resp
      ipureintro
      exact ⟨Hrn, rfl⟩


end proof

end EtcdGrove
end Perennial
