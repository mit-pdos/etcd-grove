/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/version/Manager__DowngradeValidate.lean`. Lean-first (the downgrade
API, etcd-io/etcd#22575, 2026-10-16).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.version.Manager__DowngradeValidate
public import Spec.github_com.Masterminds.semver.v3.Version__Equal
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.version.allowedDowngradeVersion

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
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.version.Assumptions]

theorem version.Manager.DowngradeValidate.wp_proof
    (hAllowed : version.allowedDowngradeVersion.spec (GF := GF) (hG := hG))
    (hEq : semver.Version.Equal.spec (GF := GF) (hG := hG)) :
    version.Manager.DowngradeValidate.spec (GF := GF) (hG := hG) := by
  intro m si γcv ctx tv
  wp_start as ⟨#Hm, #Hsrv, #Hlb, #Herr⟩
  ihave #Psv : isPkgInit (PROP := IProp GF) pkg_id.github_com.Masterminds.semver.v3 $$ []
  · iPkgInit
  iunfold version.managerIs at Hm
  iunfold version.serverOk at Hsrv
  icases Hsrv with ⟨%sv, %Hsi, #HLRN, #HGCV, #HGDI, -, -⟩
  subst Hsi
  iunfold version.dgErrVars at Herr
  icases Herr with ⟨⟨%e1, #He1⟩, ⟨%e2, #He2⟩, -⟩
  (try wp_auto)
  wp_apply HLRN $$ [] as %err -
  rcases err with ei | _
  · (try wp_auto)
    iapply HΦ; itrivial
  · (try wp_auto)
    wp_apply HGCV $$ %true [] as %cv Hcv
    · simp only [ite_true]; iexact Hlb
    icases Hcv with (%Hc | ⟨%Hcv, -⟩)
    · simp at Hc
    (try wp_auto)
    wp_apply hAllowed $$ [] as %atv %Hat
    · iframe #; ipureintro; exact Hcv
    (try wp_auto)
    wp_apply hEq $$ [] as %b -
    (try wp_auto)
    cases b
    · (try wp_auto)
      iapply HΦ; itrivial
    · (try wp_auto)
      wp_apply HGDI $$ [] as %d ⟨%Hd, %di, Hdi⟩
      (try wp_auto)
      (try wp_if_destruct)
      all_goals (try wp_auto)
      all_goals (generalize di.Enabled' = en; cases en)
      all_goals (try wp_auto)
      all_goals (iapply HΦ; itrivial)

end proof

end EtcdGrove
end Perennial
