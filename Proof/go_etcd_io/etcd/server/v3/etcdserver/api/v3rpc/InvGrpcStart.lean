/-
**etcd's gRPC server, built** (`v3rpc/grpc.go`'s `Server`; item 4 of the client→server path,
2026-10-17): the facts and objects the proofs of `v3rpc.Server` and of the constructors it calls
share. Lean-first (no Rocq counterpart); grpc's side is `Proof/google_golang_org/grpc/
InvGrpcServer.lean`.

* `ServerMethodSets` (a class, as `QuotaKVServerIsKVServer`): method-set facts, which the model
  leaves uninterpreted (`methodSet`) and Go's type checker establishes: each service value
  `Server` registers implements its service's interface (`NewQuotaKVServer` and the other
  constructors convert to it), and has no `testEmbeddedByValue` (etcd's service types embed the
  `pb.Unsafe*Server` interfaces, or a service interface, never `Unimplemented*Server` by value).
* `metricsVars` (persistent; `BaseStart.lean`): the package variables `getServerMetrics` reads:
  the mutex `metricsServerLock` guarding `metricsServerCached`, `nil` or grpc-prometheus's
  metrics. Part of `v3rpc`'s package facts (item 8, 2026-10-17: until then an assumption).
* `svcDescsOk` (persistent): the `ServiceDesc`s of etcd's six services, the generated literals
  (`rpc_grpc.pb.go`) of `etcdserverpb`'s initialization, never written: their service names,
  handler types (`(*KVServer)(nil)`, ...) and distinct method and stream names; the KV service's
  methods and the Watch service's stream exactly (the handlers `grpc.serve` runs). Part of
  `v3rpc`'s package facts, from `etcdserverpb`'s (item 8, 2026-10-17: until then an assumption).
* `GrpcCfg`, `grpcCfgOk s C` (persistent): the server's fields and configuration `Server` and its
  callees read, read-only (what `NewServer` set before the server is shared), and the server's
  contracts they take (`raftKV`, `watchSrvOk`, `srvIdsOk`, the leader, the cluster).
-/
module

public import Perennial.Golang.Theory.TypeSet
public import Proof.google_golang_org.grpc.InvGrpcServer
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvQuota
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvWatch
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvStreamInterceptor
public import Perennial.Proof.sync.Base
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvGoAttach

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api go_etcd_io.etcd.server.v3.etcdserver
  go_etcd_io.etcd.api.v3

/-- **The service values' method sets** (see the file header). -/
class v3rpc.ServerMethodSets [GooseExts] [GoGlobalContext] [GoLocalContext]
    [GoSemanticsFunctions] : Prop where
  kv_impl : go.typeSetContains (go.GoType.PointerType v3rpc.quotaKVServer.ty)
    etcdserverpb.KVServer.ty = true
  kv_te : go.typeSetContains (go.GoType.PointerType v3rpc.quotaKVServer.ty) testEmbeddedIface = false
  watch_impl : go.typeSetContains (go.GoType.PointerType v3rpc.watchServer.ty)
    etcdserverpb.WatchServer.ty = true
  watch_te : go.typeSetContains (go.GoType.PointerType v3rpc.watchServer.ty) testEmbeddedIface = false
  lease_impl : go.typeSetContains (go.GoType.PointerType v3rpc.quotaLeaseServer.ty)
    etcdserverpb.LeaseServer.ty = true
  lease_te : go.typeSetContains (go.GoType.PointerType v3rpc.quotaLeaseServer.ty)
    testEmbeddedIface = false
  cluster_impl : go.typeSetContains (go.GoType.PointerType v3rpc.ClusterServer.ty)
    etcdserverpb.ClusterServer.ty = true
  cluster_te : go.typeSetContains (go.GoType.PointerType v3rpc.ClusterServer.ty)
    testEmbeddedIface = false
  auth_impl : go.typeSetContains (go.GoType.PointerType v3rpc.AuthServer.ty)
    etcdserverpb.AuthServer.ty = true
  auth_te : go.typeSetContains (go.GoType.PointerType v3rpc.AuthServer.ty) testEmbeddedIface = false
  maint_impl : go.typeSetContains (go.GoType.PointerType v3rpc.authMaintenanceServer.ty)
    etcdserverpb.MaintenanceServer.ty = true
  maint_te : go.typeSetContains (go.GoType.PointerType v3rpc.authMaintenanceServer.ty)
    testEmbeddedIface = false

/-- `ServerMethodSets` holds, from the method sets goose emits. -/
instance v3rpc.serverMethodSets_inst [GooseExts] [GoGlobalContext] [GoLocalContext]
    [sem : go.Semantics] [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions] : v3rpc.ServerMethodSets := by
  constructor <;> (try unfold testEmbeddedIface) <;> go_type_set

section pure
variable [GooseExts] [GoGlobalContext] [GoLocalContext] [GoSemanticsFunctions]

/-- The KV service's methods `v3rpc.Server` registers, with the `*quotaKVServer` `q`: the
`(full name, MethodDesc.Handler, service value)` of `Put`, `Range`, `DeleteRange` and `Txn`
(`client/v3/Results.lean`'s `etcdKVRegs`). -/
def v3rpc.kvRegs (q : Loc) : List (GoString × GoFunc × GoInterface) :=
  [(go!"/etcdserverpb.KV/Put", (functions etcdserverpb._KV_Put_Handler []),
     interface.mkOk (go.GoType.PointerType v3rpc.quotaKVServer.ty) #q),
   (go!"/etcdserverpb.KV/Range", (functions etcdserverpb._KV_Range_Handler []),
     interface.mkOk (go.GoType.PointerType v3rpc.quotaKVServer.ty) #q),
   (go!"/etcdserverpb.KV/DeleteRange", (functions etcdserverpb._KV_DeleteRange_Handler []),
     interface.mkOk (go.GoType.PointerType v3rpc.quotaKVServer.ty) #q),
   (go!"/etcdserverpb.KV/Txn", (functions etcdserverpb._KV_Txn_Handler []),
     interface.mkOk (go.GoType.PointerType v3rpc.quotaKVServer.ty) #q),
   (go!"/etcdserverpb.KV/Compact", (functions etcdserverpb._KV_Compact_Handler []),
     interface.mkOk (go.GoType.PointerType v3rpc.quotaKVServer.ty) #q)]

/-- The Watch service's stream `v3rpc.Server` registers, with the `*watchServer` `p`. -/
def v3rpc.watchSReg (p : Loc) : GoString × GoFunc × GoInterface :=
  (go!"/etcdserverpb.Watch/Watch", (functions etcdserverpb._Watch_Watch_Handler []),
    interface.mkOk (go.GoType.PointerType v3rpc.watchServer.ty) #p)

/-- The registrations of a descriptor's methods, through their names and handlers. -/
theorem v3rpc.descRegs_eq (sn : GoString) (mds : List google_golang_org.grpc.MethodDesc)
    (ss : GoInterface) :
    descRegs sn mds ss = (mds.map fun md => (md.MethodName', md.Handler')).map
      (fun x => (grpcFullName sn x.1, x.2, ss)) := by
  simp only [descRegs, List.map_map]; rfl

/-- The registrations of a descriptor's streams, through their names and handlers. -/
theorem v3rpc.descSRegs_eq (sn : GoString) (sds : List google_golang_org.grpc.StreamDesc)
    (ss : GoInterface) :
    descSRegs sn sds ss = (sds.map fun sd => (sd.StreamName', sd.Handler')).map
      (fun x => (grpcFullName sn x.1, x.2, ss)) := by
  simp only [descSRegs, List.map_map]; rfl

/-- A function value is its `GoFunc` (`intoVal` is injective at `GoFunc`). -/
theorem v3rpc.func_intoVal_inj [go.CoreSemantics] : Function.Injective (intoVal (V := GoFunc)) := by
  intro f1 f2 h
  rw [go.intoVal_unfold GoFunc] at h
  cases f1; cases f2; cases h; rfl

/-- **Handlers from their values**: a descriptor list's names and handler values determine its
names and handlers (the generated facts state the values). -/
theorem v3rpc.handlers_eq [go.CoreSemantics] {α : Type} (N : α → GoString) (H : α → GoFunc)
    (l : List α) (l' : List (GoString × GoFunc))
    (h : l.map (fun x => (N x, (#(H x) : val))) = l'.map (fun x => (x.1, (#x.2 : val)))) :
    l.map (fun x => (N x, H x)) = l' := by
  have inj : Function.Injective (fun x : GoString × GoFunc => (x.1, (#x.2 : val))) := by
    intro a b hab
    simp only [Prod.mk.injEq] at hab
    exact Prod.ext hab.1 (v3rpc.func_intoVal_inj hab.2)
  have h' : (l.map (fun x => (N x, H x))).map (fun x : GoString × GoFunc => (x.1, (#x.2 : val))) =
      l'.map (fun x => (x.1, (#x.2 : val))) := by rw [List.map_map]; exact h
  clear h
  generalize l.map (fun x => (N x, H x)) = m at h'
  induction m generalizing l' with
  | nil => cases l' <;> simp_all
  | cons a m ih =>
    cases l' with
    | nil => simp at h'
    | cons b l' =>
      simp only [List.map_cons, List.cons.injEq] at h'
      rw [inj h'.1, ih l' h'.2]

/-- `kvDescMethods`' handlers, as `GoFunc`s. -/
def v3rpc.kvDescFuncs : List (GoString × GoFunc) :=
  [(go!"Range", functions etcdserverpb._KV_Range_Handler []),
   (go!"Put", functions etcdserverpb._KV_Put_Handler []),
   (go!"DeleteRange", functions etcdserverpb._KV_DeleteRange_Handler []),
   (go!"Txn", functions etcdserverpb._KV_Txn_Handler []),
   (go!"Compact", functions etcdserverpb._KV_Compact_Handler [])]

theorem v3rpc.kvDescMethods_eq :
    v3rpc.kvDescMethods = v3rpc.kvDescFuncs.map (fun x => (x.1, (#x.2 : val))) := rfl

/-- `authDescMethods`' handlers, as `GoFunc`s. -/
def v3rpc.authDescFuncs : List (GoString × GoFunc) :=
  [(go!"AuthEnable", functions etcdserverpb._Auth_AuthEnable_Handler []),
   (go!"AuthDisable", functions etcdserverpb._Auth_AuthDisable_Handler []),
   (go!"AuthStatus", functions etcdserverpb._Auth_AuthStatus_Handler []),
   (go!"Authenticate", functions etcdserverpb._Auth_Authenticate_Handler []),
   (go!"UserAdd", functions etcdserverpb._Auth_UserAdd_Handler []),
   (go!"UserGet", functions etcdserverpb._Auth_UserGet_Handler []),
   (go!"UserList", functions etcdserverpb._Auth_UserList_Handler []),
   (go!"UserDelete", functions etcdserverpb._Auth_UserDelete_Handler []),
   (go!"UserChangePassword", functions etcdserverpb._Auth_UserChangePassword_Handler []),
   (go!"UserGrantRole", functions etcdserverpb._Auth_UserGrantRole_Handler []),
   (go!"UserRevokeRole", functions etcdserverpb._Auth_UserRevokeRole_Handler []),
   (go!"RoleAdd", functions etcdserverpb._Auth_RoleAdd_Handler []),
   (go!"RoleGet", functions etcdserverpb._Auth_RoleGet_Handler []),
   (go!"RoleList", functions etcdserverpb._Auth_RoleList_Handler []),
   (go!"RoleDelete", functions etcdserverpb._Auth_RoleDelete_Handler []),
   (go!"RoleGrantPermission", functions etcdserverpb._Auth_RoleGrantPermission_Handler []),
   (go!"RoleRevokePermission", functions etcdserverpb._Auth_RoleRevokePermission_Handler [])]

theorem v3rpc.authDescMethods_eq :
    v3rpc.authDescMethods = v3rpc.authDescFuncs.map (fun x => (x.1, (#x.2 : val))) := rfl

/-- `leaseDescMethods`' handlers, as `GoFunc`s. -/
def v3rpc.leaseDescFuncs : List (GoString × GoFunc) :=
  [(go!"LeaseGrant", functions etcdserverpb._Lease_LeaseGrant_Handler []),
   (go!"LeaseRevoke", functions etcdserverpb._Lease_LeaseRevoke_Handler []),
   (go!"LeaseTimeToLive", functions etcdserverpb._Lease_LeaseTimeToLive_Handler []),
   (go!"LeaseLeases", functions etcdserverpb._Lease_LeaseLeases_Handler [])]

theorem v3rpc.leaseDescMethods_eq :
    v3rpc.leaseDescMethods = v3rpc.leaseDescFuncs.map (fun x => (x.1, (#x.2 : val))) := rfl

/-- **The KV service's registration contains `kvRegs`** (from the descriptor's methods). -/
theorem v3rpc.kvRegs_sub [go.CoreSemantics] (q : Loc) (mds : List google_golang_org.grpc.MethodDesc)
    (h : mds.map (fun md => (md.MethodName', (#md.Handler' : val))) = v3rpc.kvDescMethods) :
    ∀ x ∈ v3rpc.kvRegs q, x ∈ descRegs go!"etcdserverpb.KV" mds
      (interface.mkOk (go.GoType.PointerType v3rpc.quotaKVServer.ty) #q) := by
  have hF := v3rpc.handlers_eq (·.MethodName') (·.Handler') mds v3rpc.kvDescFuncs
    (by rw [h]; rfl)
  intro x hx
  rw [v3rpc.descRegs_eq, hF]
  simp only [v3rpc.kvRegs, List.mem_cons, List.not_mem_nil, or_false] at hx
  simp only [v3rpc.kvDescFuncs, List.map_cons, List.map_nil]
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
  · exact List.mem_cons_self ..
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_self ..)))
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_self ..))))

/-- The KV descriptor's names are distinct. -/
theorem v3rpc.kvDesc_nodup (mds : List google_golang_org.grpc.MethodDesc)
    (sds : List google_golang_org.grpc.StreamDesc)
    (h : mds.map (fun md => (md.MethodName', (#md.Handler' : val))) = v3rpc.kvDescMethods ∧
      sds.map (·.StreamName') = [go!"RangeStream"]) :
    (descNames mds sds).Nodup := by
  have h1 : mds.map (·.MethodName') = v3rpc.kvDescMethods.map Prod.fst := by
    rw [← h.1, List.map_map]; rfl
  simp only [descNames, h1, h.2, v3rpc.kvDescMethods, List.map_cons, List.map_nil]
  decide

/-- The Auth service's methods `v3rpc.Server` registers that `examples/etcd/auth`'s `SetUp` calls, with
the `*AuthServer` `p` (the auth plan's E3zb): `UserAdd`, `UserGrantRole`, `RoleAdd`,
`RoleGrantPermission`, `AuthEnable`, and (C1's A5, 2026-10-31) `Authenticate`, which a client's `New`
calls. -/
def v3rpc.authRegs (p : Loc) : List (GoString × GoFunc × GoInterface) :=
  [(go!"/etcdserverpb.Auth/UserAdd", (functions etcdserverpb._Auth_UserAdd_Handler []),
     interface.mkOk (go.GoType.PointerType v3rpc.AuthServer.ty) #p),
   (go!"/etcdserverpb.Auth/UserGrantRole", (functions etcdserverpb._Auth_UserGrantRole_Handler []),
     interface.mkOk (go.GoType.PointerType v3rpc.AuthServer.ty) #p),
   (go!"/etcdserverpb.Auth/RoleAdd", (functions etcdserverpb._Auth_RoleAdd_Handler []),
     interface.mkOk (go.GoType.PointerType v3rpc.AuthServer.ty) #p),
   (go!"/etcdserverpb.Auth/RoleGrantPermission", (functions etcdserverpb._Auth_RoleGrantPermission_Handler []),
     interface.mkOk (go.GoType.PointerType v3rpc.AuthServer.ty) #p),
   (go!"/etcdserverpb.Auth/AuthEnable", (functions etcdserverpb._Auth_AuthEnable_Handler []),
     interface.mkOk (go.GoType.PointerType v3rpc.AuthServer.ty) #p),
   (go!"/etcdserverpb.Auth/Authenticate", (functions etcdserverpb._Auth_Authenticate_Handler []),
     interface.mkOk (go.GoType.PointerType v3rpc.AuthServer.ty) #p)]

/-- **The Auth service's registration contains `authRegs`** (from the descriptor's methods). -/
theorem v3rpc.authRegs_sub [go.CoreSemantics] (p : Loc) (mds : List google_golang_org.grpc.MethodDesc)
    (h : mds.map (fun md => (md.MethodName', (#md.Handler' : val))) = v3rpc.authDescMethods) :
    ∀ x ∈ v3rpc.authRegs p, x ∈ descRegs go!"etcdserverpb.Auth" mds
      (interface.mkOk (go.GoType.PointerType v3rpc.AuthServer.ty) #p) := by
  have hF := v3rpc.handlers_eq (·.MethodName') (·.Handler') mds v3rpc.authDescFuncs
    (by rw [h]; rfl)
  intro x hx
  rw [v3rpc.descRegs_eq, hF]
  simp only [v3rpc.authRegs, List.mem_cons, List.not_mem_nil, or_false] at hx
  simp only [v3rpc.authDescFuncs, List.map_cons, List.map_nil]
  -- the positions of UserAdd, UserGrantRole, RoleAdd, RoleGrantPermission, AuthEnable,
  -- Authenticate
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · iterate 4 apply List.mem_cons_of_mem
    exact List.mem_cons_self ..
  · iterate 9 apply List.mem_cons_of_mem
    exact List.mem_cons_self ..
  · iterate 11 apply List.mem_cons_of_mem
    exact List.mem_cons_self ..
  · iterate 15 apply List.mem_cons_of_mem
    exact List.mem_cons_self ..
  · exact List.mem_cons_self ..
  · iterate 3 apply List.mem_cons_of_mem
    exact List.mem_cons_self ..

/-- The Auth descriptor's names are distinct. -/
theorem v3rpc.authDesc_nodup (mds : List google_golang_org.grpc.MethodDesc)
    (sds : List google_golang_org.grpc.StreamDesc)
    (h : mds.map (fun md => (md.MethodName', (#md.Handler' : val))) = v3rpc.authDescMethods ∧
      sds.map (·.StreamName') = []) :
    (descNames mds sds).Nodup := by
  have h1 : mds.map (·.MethodName') = v3rpc.authDescMethods.map Prod.fst := by
    rw [← h.1, List.map_map]; rfl
  simp only [descNames, h1, h.2, v3rpc.authDescMethods, List.map_cons, List.map_nil]
  decide

/-- **The Watch service's registration contains `watchSReg`**. -/
theorem v3rpc.watchSReg_mem [go.CoreSemantics] (p : Loc) (sds : List google_golang_org.grpc.StreamDesc)
    (h : sds.map (fun sd => (sd.StreamName', (#sd.Handler' : val))) =
      [(go!"Watch", @! etcdserverpb._Watch_Watch_Handler)]) :
    v3rpc.watchSReg p ∈ descSRegs go!"etcdserverpb.Watch" sds
      (interface.mkOk (go.GoType.PointerType v3rpc.watchServer.ty) #p) := by
  have hF := v3rpc.handlers_eq (·.StreamName') (·.Handler') sds
    [(go!"Watch", functions etcdserverpb._Watch_Watch_Handler [])] (by rw [h]; rfl)
  rw [v3rpc.descSRegs_eq, hF]
  exact List.mem_cons_self ..

/-- The Lease service's methods `v3rpc.Server` registers, with the `*quotaLeaseServer` `q` (the
lease-src plan, 2026-11-02): `LeaseGrant`, `LeaseRevoke`, `LeaseTimeToLive`, `LeaseLeases`. -/
def v3rpc.leaseRegs (q : Loc) : List (GoString × GoFunc × GoInterface) :=
  [(go!"/etcdserverpb.Lease/LeaseGrant", (functions etcdserverpb._Lease_LeaseGrant_Handler []),
     interface.mkOk (go.GoType.PointerType v3rpc.quotaLeaseServer.ty) #q),
   (go!"/etcdserverpb.Lease/LeaseRevoke", (functions etcdserverpb._Lease_LeaseRevoke_Handler []),
     interface.mkOk (go.GoType.PointerType v3rpc.quotaLeaseServer.ty) #q),
   (go!"/etcdserverpb.Lease/LeaseTimeToLive", (functions etcdserverpb._Lease_LeaseTimeToLive_Handler []),
     interface.mkOk (go.GoType.PointerType v3rpc.quotaLeaseServer.ty) #q),
   (go!"/etcdserverpb.Lease/LeaseLeases", (functions etcdserverpb._Lease_LeaseLeases_Handler []),
     interface.mkOk (go.GoType.PointerType v3rpc.quotaLeaseServer.ty) #q)]

/-- The Lease service's stream `v3rpc.Server` registers, with the `*quotaLeaseServer` `q`. -/
def v3rpc.leaseSReg (q : Loc) : GoString × GoFunc × GoInterface :=
  (go!"/etcdserverpb.Lease/LeaseKeepAlive", (functions etcdserverpb._Lease_LeaseKeepAlive_Handler []),
    interface.mkOk (go.GoType.PointerType v3rpc.quotaLeaseServer.ty) #q)

/-- **The Lease service's registration contains `leaseRegs`** (from the descriptor's methods). -/
theorem v3rpc.leaseRegs_sub [go.CoreSemantics] (q : Loc) (mds : List google_golang_org.grpc.MethodDesc)
    (h : mds.map (fun md => (md.MethodName', (#md.Handler' : val))) = v3rpc.leaseDescMethods) :
    ∀ x ∈ v3rpc.leaseRegs q, x ∈ descRegs go!"etcdserverpb.Lease" mds
      (interface.mkOk (go.GoType.PointerType v3rpc.quotaLeaseServer.ty) #q) := by
  have hF := v3rpc.handlers_eq (·.MethodName') (·.Handler') mds v3rpc.leaseDescFuncs
    (by rw [h]; rfl)
  intro x hx
  rw [v3rpc.descRegs_eq, hF]
  simp only [v3rpc.leaseRegs, List.mem_cons, List.not_mem_nil, or_false] at hx
  simp only [v3rpc.leaseDescFuncs, List.map_cons, List.map_nil]
  rcases hx with rfl | rfl | rfl | rfl
  · exact List.mem_cons_self ..
  · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_self ..)))

/-- **The Lease service's registration contains `leaseSReg`**. -/
theorem v3rpc.leaseSReg_mem [go.CoreSemantics] (q : Loc) (sds : List google_golang_org.grpc.StreamDesc)
    (h : sds.map (fun sd => (sd.StreamName', (#sd.Handler' : val))) =
      [(go!"LeaseKeepAlive", @! etcdserverpb._Lease_LeaseKeepAlive_Handler)]) :
    v3rpc.leaseSReg q ∈ descSRegs go!"etcdserverpb.Lease" sds
      (interface.mkOk (go.GoType.PointerType v3rpc.quotaLeaseServer.ty) #q) := by
  have hF := v3rpc.handlers_eq (·.StreamName') (·.Handler') sds
    [(go!"LeaseKeepAlive", functions etcdserverpb._Lease_LeaseKeepAlive_Handler [])] (by rw [h]; rfl)
  rw [v3rpc.descSRegs_eq, hF]
  exact List.mem_cons_self ..

/-- The Lease descriptor's names are distinct. -/
theorem v3rpc.leaseDesc_nodup (mds : List google_golang_org.grpc.MethodDesc)
    (sds : List google_golang_org.grpc.StreamDesc)
    (h : mds.map (fun md => (md.MethodName', (#md.Handler' : val))) = v3rpc.leaseDescMethods ∧
      sds.map (fun sd => (sd.StreamName', (#sd.Handler' : val))) =
        [(go!"LeaseKeepAlive", @! etcdserverpb._Lease_LeaseKeepAlive_Handler)]) :
    (descNames mds sds).Nodup := by
  have h1 : mds.map (·.MethodName') = v3rpc.leaseDescMethods.map Prod.fst := by
    rw [← h.1, List.map_map]; rfl
  have h2 : sds.map (·.StreamName') = [go!"LeaseKeepAlive"] := by
    rw [show (sds.map (·.StreamName')) =
      (sds.map fun sd => (sd.StreamName', (#sd.Handler' : val))).map Prod.fst by
        rw [List.map_map]; rfl, h.2]
    rfl
  simp only [descNames, h1, h2, v3rpc.leaseDescMethods, List.map_cons, List.map_nil]
  decide

/-- The Watch descriptor's names are distinct. -/
theorem v3rpc.watchDesc_nodup (sds : List google_golang_org.grpc.StreamDesc)
    (h : sds.map (fun sd => (sd.StreamName', (#sd.Handler' : val))) =
      [(go!"Watch", @! etcdserverpb._Watch_Watch_Handler)]) :
    (descNames [] sds).Nodup := by
  have h1 : sds.map (·.StreamName') = [go!"Watch"] := by
    rw [show (sds.map (·.StreamName')) =
      (sds.map fun sd => (sd.StreamName', (#sd.Handler' : val))).map Prod.fst by
        rw [List.map_map]; rfl, h]
    rfl
  simp only [descNames, List.map_nil, List.nil_append, h1]
  exact List.Pairwise.cons (fun _ h => by cases h) List.Pairwise.nil

theorem v3rpc.health_prefix : (go!"/grpc.health.v1.Health/" : GoString) =
    go!"/" ++ go!"grpc.health.v1.Health" ++ go!"/" := rfl

open google_golang_org.grpc in
/-- **The joint `Nodup` of `v3rpc.Server`'s registrations** (stage B, M2): the six services'
registrations, in `Server`'s order, and grpc's health service's, have distinct full names, from
each service's distinct method and stream names (`svcDescsOk`), the services' distinct slash-free
names (`grpcFullName_inj`) and the health service's prefix (`RegisterHealthServer`'s post). -/
theorem v3rpc.server_nodup (kmds lmds cmds amds mmds : List MethodDesc)
    (ksds wsds lsds csds asds msds : List StreamDesc) (q pw ql pc pa pm : GoInterface)
    (rs srs : List (GoString × GoFunc × GoInterface))
    (hk : (descNames kmds ksds).Nodup) (hw : (descNames [] wsds).Nodup)
    (hl : (descNames lmds lsds).Nodup) (hc : (descNames cmds csds).Nodup)
    (ha : (descNames amds asds).Nodup) (hm : (descNames mmds msds).Nodup)
    (hH : ((rs ++ srs).map Prod.fst).Nodup)
    (hHp : ∀ x ∈ rs ++ srs, go!"/grpc.health.v1.Health/" <+: x.1) :
    ((([] ++ descRegs go!"etcdserverpb.KV" kmds q ++ descRegs go!"etcdserverpb.Watch" [] pw ++
      descRegs go!"etcdserverpb.Lease" lmds ql ++ descRegs go!"etcdserverpb.Cluster" cmds pc ++
      descRegs go!"etcdserverpb.Auth" amds pa ++ rs ++ descRegs go!"etcdserverpb.Maintenance" mmds pm) ++
     ([] ++ descSRegs go!"etcdserverpb.KV" ksds q ++ descSRegs go!"etcdserverpb.Watch" wsds pw ++
      descSRegs go!"etcdserverpb.Lease" lsds ql ++ descSRegs go!"etcdserverpb.Cluster" csds pc ++
      descSRegs go!"etcdserverpb.Auth" asds pa ++ srs ++
      descSRegs go!"etcdserverpb.Maintenance" msds pm)).map Prod.fst).Nodup := by
  let S : List (GoString × List GoString × List GoString) :=
    [(go!"etcdserverpb.KV", kmds.map (·.MethodName'), ksds.map (·.StreamName')),
     (go!"etcdserverpb.Watch", ([] : List MethodDesc).map (·.MethodName'), wsds.map (·.StreamName')),
     (go!"etcdserverpb.Lease", lmds.map (·.MethodName'), lsds.map (·.StreamName')),
     (go!"etcdserverpb.Cluster", cmds.map (·.MethodName'), csds.map (·.StreamName')),
     (go!"etcdserverpb.Auth", amds.map (·.MethodName'), asds.map (·.StreamName')),
     (go!"etcdserverpb.Maintenance", mmds.map (·.MethodName'), msds.map (·.StreamName'))]
  have hperm : ((([] ++ descRegs go!"etcdserverpb.KV" kmds q ++ descRegs go!"etcdserverpb.Watch" [] pw ++
      descRegs go!"etcdserverpb.Lease" lmds ql ++ descRegs go!"etcdserverpb.Cluster" cmds pc ++
      descRegs go!"etcdserverpb.Auth" amds pa ++ rs ++ descRegs go!"etcdserverpb.Maintenance" mmds pm) ++
     ([] ++ descSRegs go!"etcdserverpb.KV" ksds q ++ descSRegs go!"etcdserverpb.Watch" wsds pw ++
      descSRegs go!"etcdserverpb.Lease" lsds ql ++ descSRegs go!"etcdserverpb.Cluster" csds pc ++
      descSRegs go!"etcdserverpb.Auth" asds pa ++ srs ++
      descSRegs go!"etcdserverpb.Maintenance" msds pm)).map Prod.fst).Perm
      (grpcNames S ++ (rs ++ srs).map Prod.fst) := by
    rw [List.perm_iff_count]
    intro a
    simp only [S, grpcNames, List.flatMap_cons, List.flatMap_nil, List.map_append,
      descRegs_names, descSRegs_names, List.count_append, List.map_nil, List.append_nil,
      List.nil_append]
    omega
  refine (List.Perm.nodup_iff hperm).mpr (List.nodup_append.mpr ⟨?_, hH, ?_⟩)
  · apply grpcNames_nodup
    · intro s hs
      simp only [S, List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨by dsimp only; decide, hk⟩
      · exact ⟨by dsimp only; decide, hw⟩
      · exact ⟨by dsimp only; decide, hl⟩
      · exact ⟨by dsimp only; decide, hc⟩
      · exact ⟨by dsimp only; decide, ha⟩
      · exact ⟨by dsimp only; decide, hm⟩
    · simp only [S, List.map_cons, List.map_nil]; decide
  · intro a ha b hb hab
    subst hab
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hb
    obtain ⟨t, ht⟩ := hHp x hx
    obtain ⟨s, hs, hsa⟩ := List.mem_flatMap.mp ha
    obtain ⟨y, _, hy⟩ := List.mem_map.mp hsa
    have hfull : x.1 = grpcFullName go!"grpc.health.v1.Health" t := by
      rw [← ht, v3rpc.health_prefix]; simp [grpcFullName, List.append_assoc]
    have hS1 : (47 : w8) ∉ s.1 ∧ s.1 ≠ go!"grpc.health.v1.Health" := by
      simp only [S, List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact ⟨by dsimp only; decide, by dsimp only; decide⟩
    have := (grpcFullName_inj s.1 go!"grpc.health.v1.Health" y t hS1.1 (by decide)
      (hy.trans hfull)).1
    exact hS1.2 this

end pure

/-- **etcd's codec is a protobuf codec** (an axiom; `v3rpc/codec.go`): `(*codec).Marshal(v)` is
`proto.Marshal(v.(proto.Message))` (golang/protobuf's, over protobuf-go's) and `Unmarshal(data, v)`
is `proto.Unmarshal(data, v.(proto.Message))`, each also adding the byte count to a prometheus
counter (`sentBytes`, `receivedBytes`); its `String()` is `"proto"`, the default codec's name. -/
axiom v3rpc.codec_proto [GooseExts] [GoGlobalContext] (l : Loc) :
  grpcProtoCodec (interface.mkOk (go.GoType.PointerType v3rpc.codec.ty) #l)

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **What `v3rpc.Server` and its callees read of the server** (a record; see the file header):
the server's contract (`raftKV` at `A`), its watchable store (`wsl`, the auth mode's tag `tag`, the apply thread's
environment `E`), its logger `lg` (`s.lg`), its configuration's logger `lg0` (`s.Cfg.Logger`), quota
`qb`, member id `mid`, transaction budget `n`, unary-request warning duration `wd`, cluster `c`,
`stopping` channel `ch`, tick and election settings `tm`, `et`, request size `m`, feature gate `fg`,
metrics level `mt`, distributed tracing switch `tr` and options `tos` (in the slice `tsl`), and the
`MaxConcurrentStreams` bound `mcs`. -/
structure v3rpc.GrpcCfg (GF : BundledGFunctors) [GooseExts] where
  A : v3rpc.KVAns GF
  E : apply.AEnv GF
  tag : GName
  wsl : Loc
  lg : Loc
  lg0 : Loc
  qb : w64
  mid : w64
  n : w64
  wd : w64
  c : Loc
  ch : Loc
  tm : w64
  et : w64
  m : w64
  fg : GoInterface
  mt : GoString
  tr : Bool
  tsl : GoSlice
  tos : List GoInterface
  mcs : w32

/-- **The server's fields and contracts `v3rpc.Server` reads** (persistent; see the file header):
read-only, as `NewServer` left them; (2026-10-31) the transaction budget within protobuf's
recursion limit (`v3rpc.maxTxnOpsOk`, `NewServer`'s configuration premise). -/
def v3rpc.grpcCfgOk (s : Loc) (C : v3rpc.GrpcCfg GF) : IProp GF :=
  iprop(v3rpc.raftKV s C.A ∗ v3rpc.watchSrvOk s C.E C.tag ∗
    srvKVAddr s ↦□ v3rpc.wsIface C.wsl ∗ v3rpc.srvIdsOk s ∗
    srvCfgFieldAddr s go!"Logger" ↦□ C.lg0 ∗ zapLoggerOk C.lg0 ∗ srvLgAddr s ↦□ C.lg ∗ zapLoggerOk C.lg ∗
    srvCfgFieldAddr s go!"QuotaBackendBytes" ↦□ C.qb ∗ srvMemberIDAddr s ↦□ C.mid ∗
    srvCfgFieldAddr s go!"MaxTxnOps" ↦□ C.n ∗ ⌜v3rpc.maxTxnOpsOk (sint.Z C.n)⌝ ∗
    srvCfgFieldAddr s go!"WarningUnaryRequestDuration" ↦□ C.wd ∗
    srvLeadInv s ∗ srvClusterAddr s ↦□ C.c ∗ membership.isRaftCluster C.c ∗
    membership.localKept C.c ∗ srvStoppingAddr s ↦□ C.ch ∗ stopChan C.ch ∗
    cfgTickMsAddr (srvCfgAddr s) ↦□ C.tm ∗ cfgElectionTicksAddr (srvCfgAddr s) ↦□ C.et ∗
    srvCfgFieldAddr s go!"MaxRequestBytes" ↦□ C.m ∗
    srvCfgFieldAddr s go!"ServerFeatureGate" ↦□ C.fg ∗ isFeatureGate C.fg ∗
    srvCfgFieldAddr s go!"Metrics" ↦□ C.mt ∗
    srvCfgFieldAddr s go!"EnableDistributedTracing" ↦□ C.tr ∗
    srvCfgFieldAddr s go!"TracerOptions" ↦□ C.tsl ∗ C.tsl ↦*□ C.tos ∗
    srvCfgFieldAddr s go!"MaxConcurrentStreams" ↦□ C.mcs)

instance v3rpc.grpcCfgOk_persistent (s : Loc) (C : v3rpc.GrpcCfg GF) :
    Persistent (v3rpc.grpcCfgOk s C) := by
  unfold v3rpc.grpcCfgOk; infer_instance

open Iris.ProofMode in
/-- **The configuration at other KV answers** (the auth component's stage 5): `grpcCfgOk` reads the
answers only through the server's contract (`raftKV`), which moves along `h`. -/
theorem v3rpc.grpcCfgOk_A (s : Loc) (C : v3rpc.GrpcCfg GF) (A' : v3rpc.KVAns GF)
    (h : v3rpc.raftKV s C.A ⊢ v3rpc.raftKV s A') :
    v3rpc.grpcCfgOk s C ⊢ v3rpc.grpcCfgOk s { C with A := A' } := by
  unfold v3rpc.grpcCfgOk
  iintro ⟨Hk, Hr⟩
  isplitl [Hk]
  · iapply h $$ Hk
  iexact Hr

end defs

end EtcdGrove
end Perennial
