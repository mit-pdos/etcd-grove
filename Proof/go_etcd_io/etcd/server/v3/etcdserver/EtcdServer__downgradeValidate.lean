/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__downgradeValidate.lean`.
Lean-first (no Rocq counterpart).
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

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem EtcdServer.downgradeValidate.wp_proof
    (hConv : convertToClusterVersion.spec (GF := GF) (hG := hG))
    (hValidate : version.Manager.DowngradeValidate.spec (GF := GF) (hG := hG))
    (hStr : semver.Version.String.spec (GF := GF) (hG := hG))
    (hCl : version.Cluster.spec (GF := GF) (hG := hG)) :
    EtcdServer.downgradeValidate.spec (GF := GF) (hG := hG) := by
  intro s l EP CP ctx v
  wp_start as ⟨#Hok, Hrd⟩
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
  (try wp_auto)
  wp_apply hConv v as %tv %err Hconv
  icases Hconv with (%Hc | ⟨%Hc, #Herr⟩)
  · obtain ⟨Hcv1, Htv, rfl⟩ := Hc
    (try wp_auto)
    wp_apply Hcv $$ %false [] as %cv Hcvr
    · simp; ipureintro; trivial
    (try wp_auto)
    wp_if_destruct
    · (try wp_auto)
      iapply HΦ
      iframe Hrd
      iunfold dgValidatePost
      iright; ileft
      isplitr
      · ipureintro; exact ⟨Hcv1, rfl⟩
      iunfold dgErrIs
      iexists eC
      iframe HeC
      ipureintro; rfl
    · have Hcvnn : cv ≠ null := Hif
      (try wp_auto)
      wp_apply hStr cv $$ [] as %str -
      · iframe #; ipureintro; exact Hcvnn
      (try wp_auto)
      wp_apply hCl as %cs -
      (try wp_auto)
      iunfold srvVersionOk at HVer
      wp_apply HVer $$ [Hrd] as %m ⟨Hrd, %vs, #Hms, #Hsrv⟩
      · iexact Hrd
      (try wp_auto)
      wp_apply hValidate m vs _ _ _ _ ctx tv $$ [] as %err Hout
      · iframe #; ipureintro; exact Htv
      (try wp_auto)
      cases err with
      | ok ei =>
        (try wp_auto)
        iapply HΦ
        iframe Hrd
        iunfold dgValidatePost
        iright; iright; ileft
        ipureintro
        exact ⟨Hcv1, rfl, fun h => by cases h⟩
      | nil =>
        (try wp_auto)
        icases typedPointsto_not_null_dup _ _ _ $$ «$r0» with ⟨Hresp, %Hrn⟩
        iapply HΦ
        iframe Hrd
        iunfold dgValidatePost
        iright; iright; iright
        iframe Hresp
        ipureintro
        exact ⟨Hcv1, Hrn, rfl⟩
  · obtain ⟨Hcv1, rfl⟩ := Hc
    ihave %Hne := dgErrIs_ne_nil _ _ $$ Herr
    cases err with
    | nil => exact absurd rfl Hne
    | ok ei =>
      (try wp_auto)
      iapply HΦ
      iframe Hrd
      iunfold dgValidatePost
      ileft
      iframe Herr
      ipureintro
      exact ⟨Hcv1, rfl⟩

end proof

end EtcdGrove
end Perennial
