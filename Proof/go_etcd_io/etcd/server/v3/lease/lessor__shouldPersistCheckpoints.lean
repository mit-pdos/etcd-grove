/-
Proof of `Spec/go_etcd_io/etcd/server/v3/lease/lessor__shouldPersistCheckpoints.lean`. Lean-first
(no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__shouldPersistCheckpoints
public import Spec.go_etcd_io.etcd.server.v3.lease.greaterOrEqual

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.lease lease

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

theorem lease.lessor.shouldPersistCheckpoints.wp_proof
    (hGE : lease.greaterOrEqual.spec (GF := GF) (hG := hG)) :
    lease.lessor.shouldPersistCheckpoints.spec (GF := GF) (hG := hG) := by
  intro lp
  wp_start as #Hcfg
  wp_auto
  iunfold lessorCfg at Hcfg
  icases Hcfg with ⟨%mt, %cpp, %cl, %ci, %lg, %rr, Hmt, Hcpp, Hcl, #Hclok, Hci, Hlg, -⟩
  iunfold clusterOk at Hclok
  icases Hclok with ⟨%cli, %Hcli, #HVer⟩
  subst Hcli
  ihave #Hver : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.version $$ []
  · iPkgInit
  ihave #Hvi : iprop((∃ v : GoString, globalAddr go_etcd_io.etcd.api.v3.version.Version ↦□ v) ∗
      (∃ v : github_com.Masterminds.semver.v3.Version,
        globalAddr go_etcd_io.etcd.api.v3.version.V3_6 ↦□ v)) $$ []
  · iapply isPkgInit_access $$ Hver
  icases Hvi with ⟨-, ⟨%v36, #Hv36⟩⟩
  wp_apply (IntoValTyped.wp_load (t := cluster.ty) _ _ _) $$ Hcl as Hcl
  wp_apply HVer as %cv Hcv
  wp_pures
  cases cpp
  · icases Hcv with (%Hnil | ⟨%ver, #Hver'⟩)
    · subst Hnil
      wp_apply (IntoValTyped.wp_load (t := go.GoType.PointerType
        github_com.Masterminds.semver.v3.Version.ty) _ _ _) $$ cv as cv
      wp_pures
      iapply HΦ; itrivial
    · ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hver'
      wp_apply (IntoValTyped.wp_load (t := go.GoType.PointerType
        github_com.Masterminds.semver.v3.Version.ty) _ _ _) $$ cv as cv
      wp_pures
      simp only [Hnn, decide_false]
      wp_pures
      wp_apply (IntoValTyped.wp_load (t := go.GoType.PointerType
        github_com.Masterminds.semver.v3.Version.ty) _ _ _) $$ cv as cv
      wp_apply hGE as %r -
      iapply HΦ; itrivial
  · wp_pures; iapply HΦ; itrivial

end proof

end EtcdGrove
end Perennial
