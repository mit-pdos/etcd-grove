/-
**etcd's unary methods and their registered message models** (phase 7 S2's interface, 2026-11-24): the
table `etcdTys` the single-process start (`grpc.start'`) sets a served address's service table with
(`grpcStartSvc ics regs etcdTys sms`, `InvGrpcRun.lean`: phase 7's switch, SW1), by full name.

The table is read off the registries (`etcdTyOf`): `etcdTyNames` names each method's request and reply
Go types, and the entry is the registered models of those types. So `etcdTys_reg` (what `grpc.start'`
asks of the table) holds by definition and rests on no registration axiom, and each method's entry
(`etcdTys_put`, ...) rests on its own two registrations only: a program's trust base holds the
registrations of the methods its proofs serve (`grpc.serve`'s premise `etcdTys m.name = some (m.Req,
m.Rep)`), which building those methods (`GrpcMethod.reqReg`/`repReg`) already needs, and no other.
(Until 2026-11-24 the table listed the models themselves and `etcdTys_reg` used all thirty
registrations, which put the Auth and lease registrations into every single-process result.)
-/
module

public import Proof.go_etcd_io.etcd.client.v3.PerTypeKVRest
public import Proof.go_etcd_io.etcd.client.v3.PerTypeLease
public import Proof.go_etcd_io.etcd.client.v3.PerTypeAuth

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **etcd's served unary methods, by full name, with their request and reply Go types.** -/
def etcdTyNames : List (GoString × go.GoType × go.GoType) :=
  [(go!"/etcdserverpb.KV/Put", etcdserverpb.PutRequest.ty, etcdserverpb.PutResponse.ty),
   (go!"/etcdserverpb.KV/Range", etcdserverpb.RangeRequest.ty, etcdserverpb.RangeResponse.ty),
   (go!"/etcdserverpb.KV/DeleteRange", etcdserverpb.DeleteRangeRequest.ty, etcdserverpb.DeleteRangeResponse.ty),
   (go!"/etcdserverpb.KV/Txn", etcdserverpb.TxnRequest.ty, etcdserverpb.TxnResponse.ty),
   (go!"/etcdserverpb.KV/Compact", etcdserverpb.CompactionRequest.ty, etcdserverpb.CompactionResponse.ty),
   (go!"/etcdserverpb.Lease/LeaseGrant", etcdserverpb.LeaseGrantRequest.ty, etcdserverpb.LeaseGrantResponse.ty),
   (go!"/etcdserverpb.Lease/LeaseRevoke", etcdserverpb.LeaseRevokeRequest.ty, etcdserverpb.LeaseRevokeResponse.ty),
   (go!"/etcdserverpb.Lease/LeaseTimeToLive", etcdserverpb.LeaseTimeToLiveRequest.ty, etcdserverpb.LeaseTimeToLiveResponse.ty),
   (go!"/etcdserverpb.Lease/LeaseLeases", etcdserverpb.LeaseLeasesRequest.ty, etcdserverpb.LeaseLeasesResponse.ty),
   (go!"/etcdserverpb.Auth/UserAdd", etcdserverpb.AuthUserAddRequest.ty, etcdserverpb.AuthUserAddResponse.ty),
   (go!"/etcdserverpb.Auth/UserGrantRole", etcdserverpb.AuthUserGrantRoleRequest.ty, etcdserverpb.AuthUserGrantRoleResponse.ty),
   (go!"/etcdserverpb.Auth/RoleAdd", etcdserverpb.AuthRoleAddRequest.ty, etcdserverpb.AuthRoleAddResponse.ty),
   (go!"/etcdserverpb.Auth/RoleGrantPermission", etcdserverpb.AuthRoleGrantPermissionRequest.ty, etcdserverpb.AuthRoleGrantPermissionResponse.ty),
   (go!"/etcdserverpb.Auth/AuthEnable", etcdserverpb.AuthEnableRequest.ty, etcdserverpb.AuthEnableResponse.ty),
   (go!"/etcdserverpb.Auth/Authenticate", etcdserverpb.AuthenticateRequest.ty, etcdserverpb.AuthenticateResponse.ty)]

open Classical in
/-- **The registered models of the request type `tq` and reply type `tp`**, when both are
registered (at models of those types). -/
def etcdTyOf (tq tp : go.GoType) : Option (ProtoMsgT GF × ProtoMsgT GF) :=
  match grpcReqModelOf GF tq, grpcRepModelOf GF tp with
  | some Rq, some Rp => if Rq.ty = tq ∧ Rp.ty = tp then some (Rq, Rp) else none
  | _, _ => none

/-- **The message models of etcd's unary method `n`**: its types' registered models. -/
def etcdTys (n : GoString) : Option (ProtoMsgT GF × ProtoMsgT GF) :=
  (etcdTyNames.find? (fun p => decide (p.1 = n))).bind fun p => etcdTyOf (GF := GF) p.2.1 p.2.2

theorem etcdTyOf_reg {tq tp : go.GoType} {Req Rep : ProtoMsgT GF}
    (h : etcdTyOf (GF := GF) tq tp = some (Req, Rep)) :
    grpcReqModelOf GF Req.ty = some Req ∧ grpcRepModelOf GF Rep.ty = some Rep := by
  unfold etcdTyOf at h
  split at h
  · next Rq Rp hq hp =>
    split at h
    · next ht =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨by rw [ht.1]; exact hq, by rw [ht.2]; exact hp⟩
    · cases h
  · cases h

theorem etcdTyOf_eq {tq tp : go.GoType} {Rq Rp : ProtoMsgT GF}
    (hq : grpcReqModelOf GF tq = some Rq) (hp : grpcRepModelOf GF tp = some Rp)
    (hqt : Rq.ty = tq) (hpt : Rp.ty = tp) : etcdTyOf (GF := GF) tq tp = some (Rq, Rp) := by
  unfold etcdTyOf
  rw [hq, hp]
  simp [hqt, hpt]

/-- **The table's models are registered** (by definition: no registration axiom). -/
theorem etcdTys_reg : ∀ (n : GoString) (Req Rep : ProtoMsgT GF), etcdTys (GF := GF) n = some (Req, Rep) →
    grpcReqModelOf GF Req.ty = some Req ∧ grpcRepModelOf GF Rep.ty = some Rep := by
  intro n Req Rep h
  unfold etcdTys at h
  obtain ⟨p, -, hp⟩ := Option.bind_eq_some_iff.1 h
  exact etcdTyOf_reg hp

/-- `Put`'s entry (from its two registrations only). -/
@[simp] theorem etcdTys_put :
    etcdTys (GF := GF) go!"/etcdserverpb.KV/Put" = some (pbPutRequestT, pbPutResponseT) := by
  have h : etcdTys (GF := GF) go!"/etcdserverpb.KV/Put" =
      etcdTyOf etcdserverpb.PutRequest.ty etcdserverpb.PutResponse.ty := by
    simp [etcdTys, etcdTyNames]
  rw [h]
  exact etcdTyOf_eq pbPutRequestT_reg pbPutResponseT_reg rfl rfl

/-- `Range`'s entry (from its two registrations only). -/
@[simp] theorem etcdTys_range :
    etcdTys (GF := GF) go!"/etcdserverpb.KV/Range" = some (pbRangeRequestT, pbRangeResponseT) := by
  have h : etcdTys (GF := GF) go!"/etcdserverpb.KV/Range" =
      etcdTyOf etcdserverpb.RangeRequest.ty etcdserverpb.RangeResponse.ty := by
    simp [etcdTys, etcdTyNames]
  rw [h]
  exact etcdTyOf_eq pbRangeRequestT_reg pbRangeResponseT_reg rfl rfl

/-- `DeleteRange`'s entry (from its two registrations only). -/
@[simp] theorem etcdTys_deleteRange :
    etcdTys (GF := GF) go!"/etcdserverpb.KV/DeleteRange" = some (pbDeleteRangeRequestT, pbDeleteRangeResponseT) := by
  have h : etcdTys (GF := GF) go!"/etcdserverpb.KV/DeleteRange" =
      etcdTyOf etcdserverpb.DeleteRangeRequest.ty etcdserverpb.DeleteRangeResponse.ty := by
    simp [etcdTys, etcdTyNames]
  rw [h]
  exact etcdTyOf_eq pbDeleteRangeRequestT_reg pbDeleteRangeResponseT_reg rfl rfl

/-- `Txn`'s entry (from its two registrations only). -/
@[simp] theorem etcdTys_txn :
    etcdTys (GF := GF) go!"/etcdserverpb.KV/Txn" = some (pbTxnRequestT, pbTxnResponseT) := by
  have h : etcdTys (GF := GF) go!"/etcdserverpb.KV/Txn" =
      etcdTyOf etcdserverpb.TxnRequest.ty etcdserverpb.TxnResponse.ty := by
    simp [etcdTys, etcdTyNames]
  rw [h]
  exact etcdTyOf_eq pbTxnRequestT_reg pbTxnResponseT_reg rfl rfl

/-- `Compact`'s entry (from its two registrations only). -/
@[simp] theorem etcdTys_compact :
    etcdTys (GF := GF) go!"/etcdserverpb.KV/Compact" = some (pbCompactionRequestT, pbCompactionResponseT) := by
  have h : etcdTys (GF := GF) go!"/etcdserverpb.KV/Compact" =
      etcdTyOf etcdserverpb.CompactionRequest.ty etcdserverpb.CompactionResponse.ty := by
    simp [etcdTys, etcdTyNames]
  rw [h]
  exact etcdTyOf_eq pbCompactionRequestT_reg pbCompactionResponseT_reg rfl rfl

/-- `LeaseGrant`'s entry (from its two registrations only). -/
@[simp] theorem etcdTys_leaseGrant :
    etcdTys (GF := GF) go!"/etcdserverpb.Lease/LeaseGrant" = some (pbLeaseGrantRequestT, pbLeaseGrantResponseT) := by
  have h : etcdTys (GF := GF) go!"/etcdserverpb.Lease/LeaseGrant" =
      etcdTyOf etcdserverpb.LeaseGrantRequest.ty etcdserverpb.LeaseGrantResponse.ty := by
    simp [etcdTys, etcdTyNames]
  rw [h]
  exact etcdTyOf_eq pbLeaseGrantRequestT_reg pbLeaseGrantResponseT_reg rfl rfl

/-- `LeaseRevoke`'s entry (from its two registrations only). -/
@[simp] theorem etcdTys_leaseRevoke :
    etcdTys (GF := GF) go!"/etcdserverpb.Lease/LeaseRevoke" = some (pbLeaseRevokeRequestT, pbLeaseRevokeResponseT) := by
  have h : etcdTys (GF := GF) go!"/etcdserverpb.Lease/LeaseRevoke" =
      etcdTyOf etcdserverpb.LeaseRevokeRequest.ty etcdserverpb.LeaseRevokeResponse.ty := by
    simp [etcdTys, etcdTyNames]
  rw [h]
  exact etcdTyOf_eq pbLeaseRevokeRequestT_reg pbLeaseRevokeResponseT_reg rfl rfl

/-- `LeaseTimeToLive`'s entry (from its two registrations only). -/
@[simp] theorem etcdTys_leaseTimeToLive :
    etcdTys (GF := GF) go!"/etcdserverpb.Lease/LeaseTimeToLive" = some (pbLeaseTimeToLiveRequestT, pbLeaseTimeToLiveResponseT) := by
  have h : etcdTys (GF := GF) go!"/etcdserverpb.Lease/LeaseTimeToLive" =
      etcdTyOf etcdserverpb.LeaseTimeToLiveRequest.ty etcdserverpb.LeaseTimeToLiveResponse.ty := by
    simp [etcdTys, etcdTyNames]
  rw [h]
  exact etcdTyOf_eq pbLeaseTimeToLiveRequestT_reg pbLeaseTimeToLiveResponseT_reg rfl rfl

/-- `LeaseLeases`'s entry (from its two registrations only). -/
@[simp] theorem etcdTys_leaseLeases :
    etcdTys (GF := GF) go!"/etcdserverpb.Lease/LeaseLeases" = some (pbLeaseLeasesRequestT, pbLeaseLeasesResponseT) := by
  have h : etcdTys (GF := GF) go!"/etcdserverpb.Lease/LeaseLeases" =
      etcdTyOf etcdserverpb.LeaseLeasesRequest.ty etcdserverpb.LeaseLeasesResponse.ty := by
    simp [etcdTys, etcdTyNames]
  rw [h]
  exact etcdTyOf_eq pbLeaseLeasesRequestT_reg pbLeaseLeasesResponseT_reg rfl rfl

/-- `UserAdd`'s entry (from its two registrations only). -/
@[simp] theorem etcdTys_userAdd :
    etcdTys (GF := GF) go!"/etcdserverpb.Auth/UserAdd" = some (pbAuthUserAddRequestT, pbAuthUserAddResponseT) := by
  have h : etcdTys (GF := GF) go!"/etcdserverpb.Auth/UserAdd" =
      etcdTyOf etcdserverpb.AuthUserAddRequest.ty etcdserverpb.AuthUserAddResponse.ty := by
    simp [etcdTys, etcdTyNames]
  rw [h]
  exact etcdTyOf_eq pbAuthUserAddRequestT_reg pbAuthUserAddResponseT_reg rfl rfl

/-- `UserGrantRole`'s entry (from its two registrations only). -/
@[simp] theorem etcdTys_userGrantRole :
    etcdTys (GF := GF) go!"/etcdserverpb.Auth/UserGrantRole" = some (pbAuthUserGrantRoleRequestT, pbAuthUserGrantRoleResponseT) := by
  have h : etcdTys (GF := GF) go!"/etcdserverpb.Auth/UserGrantRole" =
      etcdTyOf etcdserverpb.AuthUserGrantRoleRequest.ty etcdserverpb.AuthUserGrantRoleResponse.ty := by
    simp [etcdTys, etcdTyNames]
  rw [h]
  exact etcdTyOf_eq pbAuthUserGrantRoleRequestT_reg pbAuthUserGrantRoleResponseT_reg rfl rfl

/-- `RoleAdd`'s entry (from its two registrations only). -/
@[simp] theorem etcdTys_roleAdd :
    etcdTys (GF := GF) go!"/etcdserverpb.Auth/RoleAdd" = some (pbAuthRoleAddRequestT, pbAuthRoleAddResponseT) := by
  have h : etcdTys (GF := GF) go!"/etcdserverpb.Auth/RoleAdd" =
      etcdTyOf etcdserverpb.AuthRoleAddRequest.ty etcdserverpb.AuthRoleAddResponse.ty := by
    simp [etcdTys, etcdTyNames]
  rw [h]
  exact etcdTyOf_eq pbAuthRoleAddRequestT_reg pbAuthRoleAddResponseT_reg rfl rfl

/-- `RoleGrantPermission`'s entry (from its two registrations only). -/
@[simp] theorem etcdTys_roleGrantPermission :
    etcdTys (GF := GF) go!"/etcdserverpb.Auth/RoleGrantPermission" = some (pbAuthRoleGrantPermissionRequestT, pbAuthRoleGrantPermissionResponseT) := by
  have h : etcdTys (GF := GF) go!"/etcdserverpb.Auth/RoleGrantPermission" =
      etcdTyOf etcdserverpb.AuthRoleGrantPermissionRequest.ty etcdserverpb.AuthRoleGrantPermissionResponse.ty := by
    simp [etcdTys, etcdTyNames]
  rw [h]
  exact etcdTyOf_eq pbAuthRoleGrantPermissionRequestT_reg pbAuthRoleGrantPermissionResponseT_reg rfl rfl

/-- `AuthEnable`'s entry (from its two registrations only). -/
@[simp] theorem etcdTys_authEnable :
    etcdTys (GF := GF) go!"/etcdserverpb.Auth/AuthEnable" = some (pbAuthEnableRequestT, pbAuthEnableResponseT) := by
  have h : etcdTys (GF := GF) go!"/etcdserverpb.Auth/AuthEnable" =
      etcdTyOf etcdserverpb.AuthEnableRequest.ty etcdserverpb.AuthEnableResponse.ty := by
    simp [etcdTys, etcdTyNames]
  rw [h]
  exact etcdTyOf_eq pbAuthEnableRequestT_reg pbAuthEnableResponseT_reg rfl rfl

/-- `Authenticate`'s entry (from its two registrations only). -/
@[simp] theorem etcdTys_authenticate :
    etcdTys (GF := GF) go!"/etcdserverpb.Auth/Authenticate" = some (pbAuthenticateRequestT, pbAuthenticateResponseT) := by
  have h : etcdTys (GF := GF) go!"/etcdserverpb.Auth/Authenticate" =
      etcdTyOf etcdserverpb.AuthenticateRequest.ty etcdserverpb.AuthenticateResponse.ty := by
    simp [etcdTys, etcdTyNames]
  rw [h]
  exact etcdTyOf_eq pbAuthenticateRequestT_reg pbAuthenticateResponseT_reg rfl rfl

end defs

end EtcdGrove
end Perennial
