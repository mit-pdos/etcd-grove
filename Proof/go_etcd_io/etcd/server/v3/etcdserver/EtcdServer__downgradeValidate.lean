/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__downgradeValidate.lean`.
Lean-first (the downgrade API, etcd-io/etcd#22575, 2026-10-16).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__downgradeValidate
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.convertToClusterVersion
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.version.Manager__DowngradeValidate
public import Spec.github_com.Masterminds.semver.v3.Version__String
public import Spec.go_etcd_io.etcd.api.v3.version.Cluster

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

theorem EtcdServer.downgradeValidate.wp_proof
    (hConv : convertToClusterVersion.spec (GF := GF) (hG := hG))
    (hDV : version.Manager.DowngradeValidate.spec (GF := GF) (hG := hG))
    (hStr : semver.Version.String.spec (GF := GF) (hG := hG))
    (hCl : version.Cluster.spec (GF := GF) (hG := hG)) :
    EtcdServer.downgradeValidate.spec (GF := GF) (hG := hG) := by
  intro s γcv known ctx v
  wp_start as ⟨#Hcv, #Hver, #Herr, #Hverr, Hk⟩
  ihave #Psv : isPkgInit (PROP := IProp GF) pkg_id.github_com.Masterminds.semver.v3 $$ []
  · iPkgInit
  ihave #Pav : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.version $$ []
  · iPkgInit
  ihave #Pdv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.version $$ []
  · iPkgInit
  iunfold srvDgErrVars at Herr
  icases Herr with ⟨#Hcvu, #Hum, #Hwf⟩
  iunfold dgErrVar at Hcvu
  icases Hcvu with ⟨%ecvu, #Hecvu⟩
  iunfold clusterVersionAt at Hcv
  iunfold srvVersionOk at Hver
  wp_auto
  wp_apply hConv v $$ [] as %tv %err Htv
  · iframe #; iunfold srvDgErrVars; iframe #; iunfold dgErrVar; iexists ecvu; iexact Hecvu
  (try wp_auto)
  icases Htv with (%Htv | ⟨%Htv, #Hwfe⟩)
  · obtain ⟨rfl, Htvnn⟩ := Htv
    (try wp_auto)
    wp_apply Hcv $$ %known [Hk] as %cv Hcvr
    · iexact Hk
    (try wp_auto)
    wp_if_destruct
    · (try wp_auto)
      icases Hcvr with (%Hc | ⟨%Hcnn, -⟩)
      rotate_left
      · exact absurd rfl Hcnn
      have Hkf : known = false := Hc.2
      iapply HΦ
      iunfold dgOutcome
      ileft
      isplitr
      · ipureintro; exact ⟨rfl, Hkf⟩
      iunfold dgErrIs
      iexists ecvu; iframe Hecvu; ipureintro; rfl
    · icases Hcvr with (%Hc | ⟨%Hcnn, #Hlb⟩)
      · exact absurd Hc.1 (by assumption)
      (try wp_auto)
      wp_apply hStr cv $$ [] as %str -
      · iframe #; ipureintro; exact Hcnn
      (try wp_auto)
      wp_apply hCl $$ [] as %cs -
      (try wp_auto)
      wp_apply Hver $$ [] as %m ⟨%si, #Hm, #Hsi⟩
      (try wp_auto)
      wp_apply hDV m si γcv ctx tv $$ [] as %err' -
      · iframe #
      (try wp_auto)
      rcases err' with ei | _
      · (try wp_auto)
        iapply HΦ
        iunfold dgOutcome
        iright; ileft
        isplitr
        · ipureintro; simp
        simp only [Bool.false_eq_true, ite_false]; itrivial
      · (try wp_auto)
        iapply HΦ
        iunfold dgOutcome
        iright; iright
        icases typedPointsto_not_null_dup _ _ _ $$ «$r0» with ⟨Hr', %Hrnn⟩
        isplitr
        · ipureintro; exact ⟨rfl, Hrnn⟩
        iframe Hlb
        iunfold dgResp; iexists _; iexact Hr'
  · subst Htv
    iunfold dgErrIs at Hwfe
    icases Hwfe with ⟨%e, #He, %Hee⟩
    subst Hee
    (try wp_auto)
    iapply HΦ
    iunfold dgOutcome
    iright; ileft
    isplitr
    · ipureintro; simp
    simp only [Bool.false_eq_true, ite_false]; itrivial

end proof

end EtcdGrove
end Perennial
