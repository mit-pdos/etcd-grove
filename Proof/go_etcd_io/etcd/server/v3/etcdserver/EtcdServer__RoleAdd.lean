/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__RoleAdd.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__RoleAdd

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem EtcdServer.RoleAdd.wp_proof : EtcdServer.RoleAdd.spec (GF := GF) (hG := hG) := by
  intro s ctx r name P Q
  wp_start as ⟨#Hr, HP, #Hraft⟩
  (try wp_auto)
  ihave ⟨Hirr, %Hirrn⟩ := typedPointsto_not_null_dup _ _ _ $$ «$a1»
  iStructNamed Hirr
  ipersist ID
  ipersist Range
  ipersist Put
  ipersist DeleteRange
  ipersist Txn
  ipersist Compaction
  ipersist LeaseGrant
  ipersist LeaseRevoke
  ipersist Alarm
  ipersist LeaseCheckpoint
  ipersist AuthEnable
  ipersist AuthDisable
  ipersist AuthStatus
  ipersist Authenticate
  ipersist AuthUserAdd
  ipersist AuthUserDelete
  ipersist AuthUserGet
  ipersist AuthUserChangePassword
  ipersist AuthUserGrantRole
  ipersist AuthUserRevokeRole
  ipersist AuthUserList
  ipersist AuthRoleList
  ipersist AuthRoleAdd
  ipersist AuthRoleDelete
  ipersist AuthRoleGet
  ipersist AuthRoleGrantPermission
  ipersist AuthRoleRevokePermission
  ipersist ClusterVersionSet
  ipersist ClusterMemberAttrSet
  ipersist DowngradeInfoSet
  ipersist DowngradeVersionTest
  ihave #HirrNo : irrNoHdrIs «$a1_ptr» (irrRoleAdd name) $$ []
  · iunfold irrNoHdrIs
    simp only [irrRoleAdd, apply.irrEmpty, apply.optReqIs, apply.presentIs, apply.irrField]
    isplitr
    · ipureintro; exact Hirrn
    isplitr
    · have h0 : (W64 0 : w64) = 0 := by decide
      rw [h0]; iexact ID
    repeat (isplitr; · iexists _; iframe #; try (ipureintro; simp))
    iexists _; iframe #; try (ipureintro; simp)
  iunfold authRaftOk at Hraft
  ispecialize Hraft $$ %«$a1_ptr»
  wp_apply Hraft $$ [$HP $Header] as %resp %err ⟨#Herr, Hout⟩
  · iframe #
  icases Hout with (⟨%He, %l, %Hl, HQ⟩ | ⟨⟨%Hres, %He⟩, HQ⟩)
  · subst He
    subst Hl
    (try wp_auto)
    iapply HΦ
    iframe Herr
    iunfold authEntryOut
    ileft
    iframe HQ
    ipureintro; rfl
  · subst Hres
    rcases err with ei | _
    · (try wp_auto)
      iapply HΦ
      iframe Herr
      iunfold authEntryOut
      iright
      iframe HQ
      ipureintro; exact ⟨rfl, He⟩
    · exact absurd rfl He

/-- `spec`'s instance at `raftRequest.specM true` (`authRaftOk_on`). -/
theorem EtcdServer.RoleAdd.wp_proofOn
    (hRR : EtcdServer.raftRequest.specM (GF := GF) (hG := hG) true) :
    EtcdServer.RoleAdd.specOn (GF := GF) (hG := hG) := by
  intro s E ρ ctx cd r name F
  wp_start_folded as ⟨#Hreq, %Hn, HP⟩
  ihave #Hc : authRaftOk s ctx (irrRoleAdd name) etcdserverpb.AuthRoleAddResponse.ty (adminPreOn s E ρ ctx cd F)
      (adminOutOn s E ρ (irrRoleAdd name) F (adminQh ρ.kv (irrRoleAdd name)) etcdserverpb.AuthRoleAddResponse.ty) $$ []
  · iapply authRaftOk_on hRR s E ρ ctx cd (irrRoleAdd name) F _ _ rfl rfl (adminPropOk_roleAdd name Hn)
      (irrNoZeroEnd_admin _ rfl rfl rfl) (fun _ _ => .rfl)
  wp_apply EtcdServer.RoleAdd.wp_proof s ctx r name (adminPreOn s E ρ ctx cd F)
      (adminOutOn s E ρ (irrRoleAdd name) F (adminQh ρ.kv (irrRoleAdd name)) etcdserverpb.AuthRoleAddResponse.ty) $$ [HP] as %resp %err H
  · iframe # HP
  iapply HΦ
  iexact H

end proof

end EtcdGrove
end Perennial
