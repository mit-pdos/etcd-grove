/-
**etcd's unary methods and their registered message models** (phase 7 S2's interface, 2026-11-24): the
table `etcdTys` the single-process start (`grpc.start'`) sets a served address's service table with
(`grpcGoSvc ics regs etcdTys`, `InvGrpc.lean`), by full name, and its registry facts (`etcdTys_reg`,
from the models' registration axioms). Every method a served result registers is in it
(`grpc.serve`'s premise `etcdTys m.name = some (m.Req, m.Rep)`).
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

/-- **etcd's served unary methods, by full name, with their request and reply models.** -/
def etcdTyList : List (GoString × ProtoMsgT GF × ProtoMsgT GF) :=
  [(go!"/etcdserverpb.KV/Put", pbPutRequestT, pbPutResponseT),
   (go!"/etcdserverpb.KV/Range", pbRangeRequestT, pbRangeResponseT),
   (go!"/etcdserverpb.KV/DeleteRange", pbDeleteRangeRequestT, pbDeleteRangeResponseT),
   (go!"/etcdserverpb.KV/Txn", pbTxnRequestT, pbTxnResponseT),
   (go!"/etcdserverpb.KV/Compact", pbCompactionRequestT, pbCompactionResponseT),
   (go!"/etcdserverpb.Lease/LeaseGrant", pbLeaseGrantRequestT, pbLeaseGrantResponseT),
   (go!"/etcdserverpb.Lease/LeaseRevoke", pbLeaseRevokeRequestT, pbLeaseRevokeResponseT),
   (go!"/etcdserverpb.Lease/LeaseTimeToLive", pbLeaseTimeToLiveRequestT, pbLeaseTimeToLiveResponseT),
   (go!"/etcdserverpb.Lease/LeaseLeases", pbLeaseLeasesRequestT, pbLeaseLeasesResponseT),
   (go!"/etcdserverpb.Auth/UserAdd", pbAuthUserAddRequestT, pbAuthUserAddResponseT),
   (go!"/etcdserverpb.Auth/UserGrantRole", pbAuthUserGrantRoleRequestT, pbAuthUserGrantRoleResponseT),
   (go!"/etcdserverpb.Auth/RoleAdd", pbAuthRoleAddRequestT, pbAuthRoleAddResponseT),
   (go!"/etcdserverpb.Auth/RoleGrantPermission", pbAuthRoleGrantPermissionRequestT,
     pbAuthRoleGrantPermissionResponseT),
   (go!"/etcdserverpb.Auth/AuthEnable", pbAuthEnableRequestT, pbAuthEnableResponseT)]

/-- **The message models of etcd's unary method `n`** (`etcdTyList`'s entry). -/
def etcdTys (n : GoString) : Option (ProtoMsgT GF × ProtoMsgT GF) :=
  ((etcdTyList (GF := GF)).find? (fun p => decide (p.1 = n))).map (·.2)

/-- **The table's models are registered** (each by its registration axiom). -/
theorem etcdTys_reg : ∀ (n : GoString) (Req Rep : ProtoMsgT GF), etcdTys (GF := GF) n = some (Req, Rep) →
    grpcReqModelOf GF Req.ty = some Req ∧ grpcRepModelOf GF Rep.ty = some Rep := by
  intro n Req Rep h
  unfold etcdTys at h
  obtain ⟨p, hp, hpe⟩ := Option.map_eq_some_iff.1 h
  have hm := List.mem_of_find?_eq_some hp
  subst hpe
  simp only [etcdTyList, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨pbPutRequestT_reg, pbPutResponseT_reg⟩
  · exact ⟨pbRangeRequestT_reg, pbRangeResponseT_reg⟩
  · exact ⟨pbDeleteRangeRequestT_reg, pbDeleteRangeResponseT_reg⟩
  · exact ⟨pbTxnRequestT_reg, pbTxnResponseT_reg⟩
  · exact ⟨pbCompactionRequestT_reg, pbCompactionResponseT_reg⟩
  · exact ⟨pbLeaseGrantRequestT_reg, pbLeaseGrantResponseT_reg⟩
  · exact ⟨pbLeaseRevokeRequestT_reg, pbLeaseRevokeResponseT_reg⟩
  · exact ⟨pbLeaseTimeToLiveRequestT_reg, pbLeaseTimeToLiveResponseT_reg⟩
  · exact ⟨pbLeaseLeasesRequestT_reg, pbLeaseLeasesResponseT_reg⟩
  · exact ⟨pbAuthUserAddRequestT_reg, pbAuthUserAddResponseT_reg⟩
  · exact ⟨pbAuthUserGrantRoleRequestT_reg, pbAuthUserGrantRoleResponseT_reg⟩
  · exact ⟨pbAuthRoleAddRequestT_reg, pbAuthRoleAddResponseT_reg⟩
  · exact ⟨pbAuthRoleGrantPermissionRequestT_reg, pbAuthRoleGrantPermissionResponseT_reg⟩
  · exact ⟨pbAuthEnableRequestT_reg, pbAuthEnableResponseT_reg⟩

/-- A sanity check that the table's lookup computes: `Put`'s entry. -/
example : etcdTys (GF := GF) go!"/etcdserverpb.KV/Put" = some (pbPutRequestT, pbPutResponseT) := by
  simp [etcdTys, etcdTyList]

end defs

end EtcdGrove
end Perennial
