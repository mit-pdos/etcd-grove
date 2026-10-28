/-
What the gRPC server's start reads of package variables (item 8, 2026-10-17: moved here from
`InvGrpcStart.lean`, so that `v3rpc`'s package facts (`Base.lean`) can state them): the mutex
`metricsServerLock` and what it guards (`metricsVars`), and the six generated `ServiceDesc`s of
`etcdserverpb` (`svcDescsOk`), which `v3rpc`'s initializer takes from `etcdserverpb`'s fact
(`etcdserverpbDescs`, `cache/v3/Base.lean`).
-/
module

public import Proof.google_golang_org.grpc.InvGrpcServer
public import Code.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc
public import Perennial.Proof.sync.Base
public import Proof.go_etcd_io.etcd.cache.v3.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api go_etcd_io.etcd.server.v3.etcdserver
  go_etcd_io.etcd.api.v3

section pure
variable [GooseExts] [GoGlobalContext] [GoLocalContext] [GoSemanticsFunctions]

/-- The handler type of a generated `ServiceDesc` for the service interface `T`
(`(*T)(nil)`). -/
abbrev v3rpc.handlerTy (T : go.GoType) : GoInterface :=
  interface.mkOk (go.GoType.PointerType T) #(null : Loc)

/-- **The methods of the generated `KV_ServiceDesc`** (`rpc_grpc.pb.go`): `Range`, `Put`,
`DeleteRange`, `Txn`, `Compact`, with their generated handlers. -/
def v3rpc.kvDescMethods : List (GoString × val) :=
  [(go!"Range", @! etcdserverpb._KV_Range_Handler), (go!"Put", @! etcdserverpb._KV_Put_Handler),
   (go!"DeleteRange", @! etcdserverpb._KV_DeleteRange_Handler),
   (go!"Txn", @! etcdserverpb._KV_Txn_Handler), (go!"Compact", @! etcdserverpb._KV_Compact_Handler)]

/-- **The methods of the generated `Auth_ServiceDesc`** (`rpc_grpc.pb.go`), with their generated
handlers (the auth plan's E3zb). -/
def v3rpc.authDescMethods : List (GoString × val) :=
  [(go!"AuthEnable", @! etcdserverpb._Auth_AuthEnable_Handler),
   (go!"AuthDisable", @! etcdserverpb._Auth_AuthDisable_Handler),
   (go!"AuthStatus", @! etcdserverpb._Auth_AuthStatus_Handler),
   (go!"Authenticate", @! etcdserverpb._Auth_Authenticate_Handler),
   (go!"UserAdd", @! etcdserverpb._Auth_UserAdd_Handler),
   (go!"UserGet", @! etcdserverpb._Auth_UserGet_Handler),
   (go!"UserList", @! etcdserverpb._Auth_UserList_Handler),
   (go!"UserDelete", @! etcdserverpb._Auth_UserDelete_Handler),
   (go!"UserChangePassword", @! etcdserverpb._Auth_UserChangePassword_Handler),
   (go!"UserGrantRole", @! etcdserverpb._Auth_UserGrantRole_Handler),
   (go!"UserRevokeRole", @! etcdserverpb._Auth_UserRevokeRole_Handler),
   (go!"RoleAdd", @! etcdserverpb._Auth_RoleAdd_Handler),
   (go!"RoleGet", @! etcdserverpb._Auth_RoleGet_Handler),
   (go!"RoleList", @! etcdserverpb._Auth_RoleList_Handler),
   (go!"RoleDelete", @! etcdserverpb._Auth_RoleDelete_Handler),
   (go!"RoleGrantPermission", @! etcdserverpb._Auth_RoleGrantPermission_Handler),
   (go!"RoleRevokePermission", @! etcdserverpb._Auth_RoleRevokePermission_Handler)]

/-- `getServerMetrics`'s lock (the package variable `metricsServerLock`). -/
abbrev v3rpc.metricsMu : Loc := globalAddr go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.metricsServerLock

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- What `metricsServerLock` guards: `metricsServerCached`, `nil` or metrics. -/
def v3rpc.metricsP : IProp GF :=
  iprop(∃ m : Loc,
    globalAddr go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.metricsServerCached ↦ m ∗
    (⌜m = null⌝ ∨ promSrvMetrics m))

/-- **The package variables of `getServerMetrics`** (persistent; see the file header). -/
def v3rpc.metricsVars : IProp GF :=
  iprop(sync.isMutex v3rpc.metricsMu v3rpc.metricsP)

instance v3rpc.metricsVars_persistent : Persistent (v3rpc.metricsVars (GF := GF)) := by
  unfold v3rpc.metricsVars; infer_instance

/-- **A generated `ServiceDesc`** at `d` (persistent): the service `sn`, the handler type
`(*T)(nil)`, some methods and streams with distinct names. -/
def v3rpc.descOk (d : Loc) (sn : GoString) (T : go.GoType) : IProp GF :=
  iprop(∃ (mds : List google_golang_org.grpc.MethodDesc)
      (sds : List google_golang_org.grpc.StreamDesc),
    go_etcd_io.etcd.cache.v3.pbDescIs d sn (v3rpc.handlerTy T) mds sds ∗ ⌜(descNames mds sds).Nodup⌝)

instance v3rpc.descOk_persistent (d : Loc) (sn : GoString) (T : go.GoType) :
    Persistent (v3rpc.descOk (GF := GF) d sn T) := by
  unfold v3rpc.descOk; infer_instance

/-- **The six `ServiceDesc`s `v3rpc.Server` registers** (persistent; see the file header). -/
def v3rpc.svcDescsOk : IProp GF :=
  iprop((∃ (mds : List google_golang_org.grpc.MethodDesc)
        (sds : List google_golang_org.grpc.StreamDesc),
      go_etcd_io.etcd.cache.v3.pbDescIs (globalAddr etcdserverpb.KV_ServiceDesc) go!"etcdserverpb.KV"
        (v3rpc.handlerTy etcdserverpb.KVServer.ty) mds sds ∗
      ⌜mds.map (fun md => (md.MethodName', (#md.Handler' : val))) = v3rpc.kvDescMethods ∧
        sds.map (·.StreamName') = [go!"RangeStream"]⌝) ∗
    (∃ (sds : List google_golang_org.grpc.StreamDesc),
      go_etcd_io.etcd.cache.v3.pbDescIs (globalAddr etcdserverpb.Watch_ServiceDesc) go!"etcdserverpb.Watch"
        (v3rpc.handlerTy etcdserverpb.WatchServer.ty) [] sds ∗
      ⌜sds.map (fun sd => (sd.StreamName', (#sd.Handler' : val))) =
        [(go!"Watch", @! etcdserverpb._Watch_Watch_Handler)]⌝) ∗
    v3rpc.descOk (globalAddr etcdserverpb.Lease_ServiceDesc) go!"etcdserverpb.Lease"
      etcdserverpb.LeaseServer.ty ∗
    v3rpc.descOk (globalAddr etcdserverpb.Cluster_ServiceDesc) go!"etcdserverpb.Cluster"
      etcdserverpb.ClusterServer.ty ∗
    (∃ (mds : List google_golang_org.grpc.MethodDesc)
        (sds : List google_golang_org.grpc.StreamDesc),
      go_etcd_io.etcd.cache.v3.pbDescIs (globalAddr etcdserverpb.Auth_ServiceDesc) go!"etcdserverpb.Auth"
        (v3rpc.handlerTy etcdserverpb.AuthServer.ty) mds sds ∗
      ⌜mds.map (fun md => (md.MethodName', (#md.Handler' : val))) = v3rpc.authDescMethods ∧
        sds.map (·.StreamName') = []⌝) ∗
    v3rpc.descOk (globalAddr etcdserverpb.Maintenance_ServiceDesc) go!"etcdserverpb.Maintenance"
      etcdserverpb.MaintenanceServer.ty)

instance v3rpc.svcDescsOk_persistent : Persistent (v3rpc.svcDescsOk (GF := GF)) := by
  unfold v3rpc.svcDescsOk; infer_instance

end defs

section defsLC
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- A generated `ServiceDesc` as `etcdserverpb`'s fact states it is one as grpc's proofs take it. -/
theorem v3rpc.pbDescIs_grpc (sd : Loc) (sn : GoString) (ht : GoInterface)
    (mds : List google_golang_org.grpc.MethodDesc) (sds : List google_golang_org.grpc.StreamDesc) :
    go_etcd_io.etcd.cache.v3.pbDescIs (GF := GF) sd sn ht mds sds ⊢ grpcDescIs sd sn ht mds sds := by
  unfold go_etcd_io.etcd.cache.v3.pbDescIs grpcDescIs
  exact .rfl

end defsLC

end EtcdGrove
end Perennial
