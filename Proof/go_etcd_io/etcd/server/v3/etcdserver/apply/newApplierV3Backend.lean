/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.newApplierV3Backend
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend__Apply
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend__Put
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend__DeleteRange
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend__Range
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend__Txn
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend__LeaseRevoke
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend__LeaseGrant
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend__LeaseCheckpoint
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend__Alarm
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend__Authenticate
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend__UserAdd
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend__UserDelete
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend__UserChangePassword
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend__UserGrantRole
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend__UserGet
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend__UserRevokeRole
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend__RoleAdd
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend__RoleGrantPermission
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend__RoleGet
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend__RoleRevokePermission
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend__RoleDelete
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend__UserList
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend__RoleList
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend__AuthEnable
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend__AuthDisable
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend__AuthStatus
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend__ClusterVersionSet
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend__ClusterMemberAttrSet
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend__DowngradeInfoSet
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend__Compaction
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Packaging

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.apply go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

theorem apply.newApplierV3Backend.wp_proof
    (hApply : apply.applierV3backend.Apply.spec (GF := GF) (hG := hG))
    (hPut : apply.applierV3backend.Put.spec (GF := GF) (hG := hG))
    (hDeleteRange : apply.applierV3backend.DeleteRange.spec (GF := GF) (hG := hG))
    (hRange : apply.applierV3backend.Range.spec (GF := GF) (hG := hG))
    (hTxn : apply.applierV3backend.Txn.spec (GF := GF) (hG := hG))
    (hLeaseRevoke : apply.applierV3backend.LeaseRevoke.spec (GF := GF) (hG := hG))
    (hLeaseGrant : apply.applierV3backend.LeaseGrant.spec (GF := GF) (hG := hG))
    (hLeaseCheckpoint : apply.applierV3backend.LeaseCheckpoint.spec (GF := GF) (hG := hG))
    (hAlarm : apply.applierV3backend.Alarm.spec (GF := GF) (hG := hG))
    (hAuthenticate : apply.applierV3backend.Authenticate.spec (GF := GF) (hG := hG))
    (hUserAdd : apply.applierV3backend.UserAdd.spec (GF := GF) (hG := hG))
    (hUserDelete : apply.applierV3backend.UserDelete.spec (GF := GF) (hG := hG))
    (hUserChangePassword : apply.applierV3backend.UserChangePassword.spec (GF := GF) (hG := hG))
    (hUserGrantRole : apply.applierV3backend.UserGrantRole.spec (GF := GF) (hG := hG))
    (hUserGet : apply.applierV3backend.UserGet.spec (GF := GF) (hG := hG))
    (hUserRevokeRole : apply.applierV3backend.UserRevokeRole.spec (GF := GF) (hG := hG))
    (hRoleAdd : apply.applierV3backend.RoleAdd.spec (GF := GF) (hG := hG))
    (hRoleGrantPermission : apply.applierV3backend.RoleGrantPermission.spec (GF := GF) (hG := hG))
    (hRoleGet : apply.applierV3backend.RoleGet.spec (GF := GF) (hG := hG))
    (hRoleRevokePermission : apply.applierV3backend.RoleRevokePermission.spec (GF := GF) (hG := hG))
    (hRoleDelete : apply.applierV3backend.RoleDelete.spec (GF := GF) (hG := hG))
    (hUserList : apply.applierV3backend.UserList.spec (GF := GF) (hG := hG))
    (hRoleList : apply.applierV3backend.RoleList.spec (GF := GF) (hG := hG))
    (hAuthEnable : apply.applierV3backend.AuthEnable.spec (GF := GF) (hG := hG))
    (hAuthDisable : apply.applierV3backend.AuthDisable.spec (GF := GF) (hG := hG))
    (hAuthStatus : apply.applierV3backend.AuthStatus.spec (GF := GF) (hG := hG))
    (hClusterVersionSet : apply.applierV3backend.ClusterVersionSet.spec (GF := GF) (hG := hG))
    (hClusterMemberAttrSet : apply.applierV3backend.ClusterMemberAttrSet.spec (GF := GF) (hG := hG))
    (hDowngradeInfoSet : apply.applierV3backend.DowngradeInfoSet.spec (GF := GF) (hG := hG))
    (hCompaction : apply.applierV3backend.Compaction.spec (GF := GF) (hG := hG))
    : apply.newApplierV3Backend.spec (GF := GF) (hG := hG) := by
  intro opts
  wp_start
  wp_auto
  wp_alloc p as Hp
  iStructNamed Hp
  ipersist options
  wp_auto
  iapply HΦ
  isplitr
  · iexists p; iframe options; ipureintro; rfl
  iintro !> %E #Hopts
  ihave #Hbk : apply.backendIs E p $$ []
  · iunfold apply.backendIs
    iexists opts
    iframe #
  iunfold apply.applierSpec
  iexists ⟨go.GoType.PointerType applierV3backend.ty, #p⟩
  isplitr
  · ipureintro; rfl
  iunfold apply.applierTriples
  isplitr
  · imodintro
    iintro %r %rq %o %log %F %Pre %Q %Post %info
    imodintro
    iintro %Φ' ⟨Hpre, #HF⟩ HΦ'
    iapply (hPut E p r rq o log F Pre Q Post info) $$ [Hpre] HΦ'
    iframe Hpre
    iframe #
  isplitr
  · imodintro
    iintro %r %rq %o %log %F %Pre %Q %Post %info
    imodintro
    iintro %Φ' ⟨Hpre, #HF⟩ HΦ'
    iapply (hDeleteRange E p r rq o log F Pre Q Post info) $$ [Hpre] HΦ'
    iframe Hpre
    iframe #
  isplitr
  · imodintro
    iintro %r %rq %o %log %info
    imodintro
    iintro %Φ' Hpre HΦ'
    iapply (hRange E p r rq o log info) $$ [Hpre] HΦ'
    iframe Hpre
    iframe #
  isplitr
  · imodintro
    iintro %r %skip %rq %t %log %F %Pre %Q %Post %info
    imodintro
    iintro %Φ' ⟨Hpre, #HF⟩ HΦ'
    iapply (hTxn E p r skip rq t log F Pre Q Post info) $$ [Hpre] HΦ'
    iframe Hpre
    iframe #
  isplitr
  · imodintro
    iintro %r %rq %id %log %Pre %Q %Post %info
    imodintro
    iintro %Φ' Hpre HΦ'
    iapply (hLeaseRevoke E p r rq id log Pre Q Post info) $$ [Hpre] HΦ'
    iframe Hpre
    iframe #
  isplitr
  · imodintro
    iintro %m %r %log %Pre %Q %Post %info %hm
    imodintro
    iintro %Φ' Hpre HΦ'
    simp only [apply.respMethods, List.mem_cons, List.not_mem_nil, _root_.or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
    all_goals simp (config := {decide := true}) only [apply.reqFacts, ↓reduceIte]
    · icases Hpre with ⟨HR, Hm, Hwt, #Hsp⟩
      iapply (hLeaseGrant E p r log Pre Q Post info) $$ [HR Hm Hwt] HΦ'
      iframe
      iframe #
    · icases Hpre with ⟨HR, Hm, Hwt, #Hsp⟩
      iapply (hLeaseCheckpoint E p r log Pre Q Post info) $$ [HR Hm Hwt] HΦ'
      iframe
      iframe #
    · icases Hpre with ⟨HR, Hm, Hwt, #Hsp⟩
      iapply (hAlarm E p r log Pre Q Post info) $$ [HR Hm Hwt] HΦ'
      iframe
      iframe #
    · icases Hpre with ⟨HR, Hm, Hwt, #Hsp⟩
      iapply (hAuthenticate E p r log Pre Q Post info) $$ [HR Hm Hwt] HΦ'
      iframe
      iframe #
    · icases Hpre with ⟨HR, Hm, Hwt, #Hsp⟩
      iapply (hUserAdd E p r log Pre Q Post info) $$ [HR Hm Hwt] HΦ'
      iframe
      iframe #
    · icases Hpre with ⟨HR, Hm, Hwt, #Hsp⟩
      iapply (hUserDelete E p r log Pre Q Post info) $$ [HR Hm Hwt] HΦ'
      iframe
      iframe #
    · icases Hpre with ⟨HR, Hm, Hwt, #Hsp⟩
      iapply (hUserChangePassword E p r log Pre Q Post info) $$ [HR Hm Hwt] HΦ'
      iframe
      iframe #
    · icases Hpre with ⟨HR, Hm, Hwt, #Hsp⟩
      iapply (hUserGrantRole E p r log Pre Q Post info) $$ [HR Hm Hwt] HΦ'
      iframe
      iframe #
    · icases Hpre with ⟨HR, Hm, Hwt, #Hsp⟩
      iapply (hUserGet E p r log Pre Q Post info) $$ [HR Hm Hwt] HΦ'
      iframe
      iframe #
    · icases Hpre with ⟨HR, Hm, Hwt, #Hsp⟩
      iapply (hUserRevokeRole E p r log Pre Q Post info) $$ [HR Hm Hwt] HΦ'
      iframe
      iframe #
    · icases Hpre with ⟨HR, Hm, Hwt, #Hsp⟩
      iapply (hRoleAdd E p r log Pre Q Post info) $$ [HR Hm Hwt] HΦ'
      iframe
      iframe #
    · icases Hpre with ⟨HR, Hm, Hwt, #Hsp⟩
      iapply (hRoleGrantPermission E p r log Pre Q Post info) $$ [HR Hm Hwt] HΦ'
      iframe
      iframe #
    · icases Hpre with ⟨HR, Hm, Hwt, #Hsp⟩
      iapply (hRoleGet E p r log Pre Q Post info) $$ [HR Hm Hwt] HΦ'
      iframe
      iframe #
    · icases Hpre with ⟨HR, Hm, Hwt, #Hsp⟩
      iapply (hRoleRevokePermission E p r log Pre Q Post info) $$ [HR Hm Hwt] HΦ'
      iframe
      iframe #
    · icases Hpre with ⟨HR, Hm, Hwt, #Hsp⟩
      iapply (hRoleDelete E p r log Pre Q Post info) $$ [HR Hm Hwt] HΦ'
      iframe
      iframe #
    · icases Hpre with ⟨HR, Hm, Hwt, #Hsp⟩
      iapply (hUserList E p r log Pre Q Post info) $$ [HR Hm Hwt] HΦ'
      iframe
      iframe #
    · icases Hpre with ⟨HR, Hm, Hwt, #Hsp⟩
      iapply (hRoleList E p r log Pre Q Post info) $$ [HR Hm Hwt] HΦ'
      iframe
      iframe #
  isplitr
  · -- `AuthEnable`, `AuthDisable`
    imodintro
    iintro %m %log %Pre %Q %Post %info %hm %hon
    imodintro
    iintro %Φ' Hpre HΦ'
    simp only [apply.resp0Methods, List.mem_cons, List.not_mem_nil, _root_.or_false] at hm
    rcases hm with rfl | rfl
    · iapply (hAuthEnable E p log Pre Q Post info) $$ [Hpre] HΦ'
      iframe
      iframe #
      try (ipureintro; exact ⟨hon.2, hon.1 rfl⟩)
    · iapply (hAuthDisable E p log Pre Q Post info) $$ [Hpre] HΦ'
      iframe
      iframe #
      try (ipureintro; exact hon.2)
  isplitr
  · -- `AuthStatus`
    imodintro
    iintro %log %info
    imodintro
    iintro %Φ' ⟨Hkv, -⟩ HΦ'
    iapply (hAuthStatus E p log) $$ [Hkv]
    · iframe
      iframe #
    inext
    iintro %resp %err ⟨Hkv, #HeI⟩
    iapply HΦ'
    iframe Hkv HeI
    simp only [apply.chainRes]
    ipureintro; trivial
  isplitr
  · -- the cluster's methods
    imodintro
    iintro %m %r %v3 %log %Pre %Q %Post %cr %rs %info %hm
    imodintro
    iintro %Φ' Hpre HΦ'
    icases Hpre with ⟨HR, Hm, Hwt, HFS, HRO⟩
    cases cr with
    | ver v =>
      iunfold apply.clusterFacts at HR
      icases HR with ⟨%Hmv, #HR, %Hsv⟩
      subst Hmv
      iapply (hClusterVersionSet E p r v3 log Pre Q Post v rs info) $$ [Hm Hwt HFS HRO] [HΦ']
      · iframe
        iframe #
        ipureintro; exact Hsv
      inext
      iintro ⟨H1, H2, H3⟩
      iapply HΦ'
      iframe
    | attr a =>
      iunfold apply.clusterFacts at HR
      icases HR with ⟨%Hmv, #HR⟩
      subst Hmv
      iapply (hClusterMemberAttrSet E p r v3 log Pre Q Post a rs info) $$ [Hm Hwt HRO] [HΦ' HFS]
      · iframe
        iframe #
      inext
      iintro ⟨Hpost, HRO⟩
      iapply HΦ'
      iframe
    | dg d =>
      iunfold apply.clusterFacts at HR
      icases HR with ⟨%Hmv, #HR, HRW⟩
      subst Hmv
      iapply (hDowngradeInfoSet E p r v3 log Pre Q Post info) $$ [Hm Hwt HRW] [HΦ' HFS HRO]
      · iframe
        iframe #
      inext
      iintro Hpost
      iapply HΦ'
      iframe
  isplitr
  · -- `Apply`: the backend's, its `applyFunc` with the chain's (empty) resources
    imodintro
    iintro %r %rq %skip %v3 %af %A %B
    imodintro
    iintro %Φ' ⟨#Hw, HA, #Haf⟩ HΦ'
    iapply (hApply p r v3 af (iprop(apply.chainRes .backend
        (.ok ⟨go.GoType.PointerType applierV3backend.ty, #p⟩) (apply.principalOf rq) ∗ A))
      (fun ar => iprop(apply.chainResAny .backend
        (.ok ⟨go.GoType.PointerType applierV3backend.ty, #p⟩) ∗ B ar))) $$ [HA]
    · iframe #
      iframe HA
      simp only [apply.chainRes]
      ipureintro; trivial
    inext
    iintro %ar ⟨-, HB⟩
    iapply HΦ'
    ileft
    iframe HB
    iapply apply.adminPass_off
    rfl
  · -- `Compaction`: the backend's
    iunfold apply.cmpTriple
    imodintro
    iintro %cr %rev %log %crev %Pre %Q %Post %info
    imodintro
    iintro %Φ' Hpre HΦ'
    iapply (hCompaction E p cr rev log crev Pre Q Post info) $$ [Hpre]
    · iframe Hpre; iframe #
    inext
    iintro %resp %ch %trace %err ⟨Hkv, HPP, Hc, Hans⟩
    iapply HΦ'
    simp only [apply.chainCompacts, ↓reduceIte, apply.chainRes]
    iframe Hkv HPP Hc Hans

end proof

end EtcdGrove
end Perennial
