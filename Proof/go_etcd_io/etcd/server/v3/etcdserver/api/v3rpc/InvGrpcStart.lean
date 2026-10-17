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
* `metricsVars` (persistent): the package variables `getServerMetrics` reads: the mutex
  `metricsServerLock` guarding `metricsServerCached`, `nil` or grpc-prometheus's metrics. An
  assumption about package initialization (`metricsServerLock`'s zero value is an unlocked
  mutex, `metricsServerCached`'s `nil`), as `watchVars`.
* `svcDescsOk` (persistent): the `ServiceDesc`s of etcd's six services, the generated literals
  (`rpc_grpc.pb.go`) of `etcdserverpb`'s initialization, never written: their service names,
  handler types (`(*KVServer)(nil)`, ...) and distinct method and stream names; the KV service's
  methods and the Watch service's stream exactly (the handlers `grpc.serve` runs). An assumption
  about package initialization, as `watchDescOk`.
* `GrpcCfg`, `grpcCfgOk s C` (persistent): the server's fields and configuration `Server` and its
  callees read, read-only (what `NewServer` set before the server is shared), and the server's
  contracts they take (`raftKV`, `watchSrvOk`, `srvIdsOk`, the leader, the cluster).
-/
module

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
class v3rpc.ServerMethodSets [FfiSyntax] [GoGlobalContext] [GoLocalContext]
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

section pure
variable [FfiSyntax] [GoGlobalContext] [GoLocalContext] [GoSemanticsFunctions]

/-- The KV service's methods `v3rpc.Server` registers, with the `*quotaKVServer` `q`: the
`(full name, MethodDesc.Handler, service value)` of `Put`, `Range`, `DeleteRange` and `Txn`
(`client/v3/Results.lean`'s `etcdKVRegs`). -/
def v3rpc.kvRegs (q : Loc) : List (GoString × val × GoInterface) :=
  [(go!"/etcdserverpb.KV/Put", (@! etcdserverpb._KV_Put_Handler),
     interface.mkOk (go.GoType.PointerType v3rpc.quotaKVServer.ty) #q),
   (go!"/etcdserverpb.KV/Range", (@! etcdserverpb._KV_Range_Handler),
     interface.mkOk (go.GoType.PointerType v3rpc.quotaKVServer.ty) #q),
   (go!"/etcdserverpb.KV/DeleteRange", (@! etcdserverpb._KV_DeleteRange_Handler),
     interface.mkOk (go.GoType.PointerType v3rpc.quotaKVServer.ty) #q),
   (go!"/etcdserverpb.KV/Txn", (@! etcdserverpb._KV_Txn_Handler),
     interface.mkOk (go.GoType.PointerType v3rpc.quotaKVServer.ty) #q)]

/-- The Watch service's stream `v3rpc.Server` registers, with the `*watchServer` `p`. -/
def v3rpc.watchSReg (p : Loc) : GoString × val × GoInterface :=
  (go!"/etcdserverpb.Watch/Watch", (@! etcdserverpb._Watch_Watch_Handler),
    interface.mkOk (go.GoType.PointerType v3rpc.watchServer.ty) #p)

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

/-- `getServerMetrics`'s lock (the package variable `metricsServerLock`). -/
abbrev v3rpc.metricsMu : Loc := globalAddr go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.metricsServerLock

/-- The registrations of a descriptor's methods, through their names and handlers. -/
theorem v3rpc.descRegs_eq (sn : GoString) (mds : List google_golang_org.grpc.MethodDesc)
    (ss : GoInterface) :
    descRegs sn mds ss = (mds.map fun md => (md.MethodName', (#md.Handler' : val))).map
      (fun x => (grpcFullName sn x.1, x.2, ss)) := by
  simp only [descRegs, List.map_map]; rfl

/-- **The KV service's registration contains `kvRegs`** (from the descriptor's methods). -/
theorem v3rpc.kvRegs_sub (q : Loc) (mds : List google_golang_org.grpc.MethodDesc)
    (h : mds.map (fun md => (md.MethodName', (#md.Handler' : val))) = v3rpc.kvDescMethods) :
    ∀ x ∈ v3rpc.kvRegs q, x ∈ descRegs go!"etcdserverpb.KV" mds
      (interface.mkOk (go.GoType.PointerType v3rpc.quotaKVServer.ty) #q) := by
  intro x hx
  rw [v3rpc.descRegs_eq, h]
  simp only [v3rpc.kvRegs, List.mem_cons, List.not_mem_nil, or_false] at hx
  simp only [v3rpc.kvDescMethods, List.map_cons, List.map_nil]
  rcases hx with rfl | rfl | rfl | rfl
  · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
  · exact List.mem_cons_self ..
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_self ..)))

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

/-- **The Watch service's registration contains `watchSReg`**. -/
theorem v3rpc.watchSReg_mem (p : Loc) (sds : List google_golang_org.grpc.StreamDesc)
    (h : sds.map (fun sd => (sd.StreamName', (#sd.Handler' : val))) =
      [(go!"Watch", @! etcdserverpb._Watch_Watch_Handler)]) :
    v3rpc.watchSReg p ∈ descSRegs go!"etcdserverpb.Watch" sds
      (interface.mkOk (go.GoType.PointerType v3rpc.watchServer.ty) #p) := by
  have e : descSRegs go!"etcdserverpb.Watch" sds
      (interface.mkOk (go.GoType.PointerType v3rpc.watchServer.ty) #p) =
      (sds.map fun sd => (sd.StreamName', (#sd.Handler' : val))).map
        (fun x => (grpcFullName go!"etcdserverpb.Watch" x.1, x.2,
          interface.mkOk (go.GoType.PointerType v3rpc.watchServer.ty) #p)) := by
    simp only [descSRegs, List.map_map]; rfl
  rw [e, h]
  exact List.mem_cons_self ..

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

end pure

/-- **etcd's codec is a protobuf codec** (an axiom; `v3rpc/codec.go`): `(*codec).Marshal(v)` is
`proto.Marshal(v.(proto.Message))` (golang/protobuf's, over protobuf-go's) and `Unmarshal(data, v)`
is `proto.Unmarshal(data, v.(proto.Message))`, each also adding the byte count to a prometheus
counter (`sentBytes`, `receivedBytes`); its `String()` is `"proto"`, the default codec's name. -/
axiom v3rpc.codec_proto [FfiSyntax] [GoGlobalContext] (l : Loc) :
  grpcProtoCodec (interface.mkOk (go.GoType.PointerType v3rpc.codec.ty) #l)

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- What `metricsServerLock` guards: `metricsServerCached`, `nil` or metrics. -/
def v3rpc.metricsP : IProp GF :=
  iprop(∃ m : Loc,
    globalAddr go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.metricsServerCached ↦ m ∗
    (⌜m = null⌝ ∨ promSrvMetrics m))

/-- **The package variables of `getServerMetrics`** (persistent; see the file header). -/
def v3rpc.metricsVars : IProp GF :=
  iprop(sync.isMutex (hlc := HasLC.hasLC) v3rpc.metricsMu v3rpc.metricsP)

instance v3rpc.metricsVars_persistent : Persistent (v3rpc.metricsVars (GF := GF)) := by
  unfold v3rpc.metricsVars; infer_instance

/-- **A generated `ServiceDesc`** at `d` (persistent): the service `sn`, the handler type
`(*T)(nil)`, some methods and streams with distinct names. -/
def v3rpc.descOk (d : Loc) (sn : GoString) (T : go.GoType) : IProp GF :=
  iprop(∃ (mds : List google_golang_org.grpc.MethodDesc)
      (sds : List google_golang_org.grpc.StreamDesc),
    grpcDescIs d sn (v3rpc.handlerTy T) mds sds ∗ ⌜(descNames mds sds).Nodup⌝)

instance v3rpc.descOk_persistent (d : Loc) (sn : GoString) (T : go.GoType) :
    Persistent (v3rpc.descOk (GF := GF) d sn T) := by
  unfold v3rpc.descOk; infer_instance

/-- **The six `ServiceDesc`s `v3rpc.Server` registers** (persistent; see the file header). -/
def v3rpc.svcDescsOk : IProp GF :=
  iprop((∃ (mds : List google_golang_org.grpc.MethodDesc)
        (sds : List google_golang_org.grpc.StreamDesc),
      grpcDescIs (globalAddr etcdserverpb.KV_ServiceDesc) go!"etcdserverpb.KV"
        (v3rpc.handlerTy etcdserverpb.KVServer.ty) mds sds ∗
      ⌜mds.map (fun md => (md.MethodName', (#md.Handler' : val))) = v3rpc.kvDescMethods ∧
        sds.map (·.StreamName') = [go!"RangeStream"]⌝) ∗
    (∃ (sds : List google_golang_org.grpc.StreamDesc),
      grpcDescIs (globalAddr etcdserverpb.Watch_ServiceDesc) go!"etcdserverpb.Watch"
        (v3rpc.handlerTy etcdserverpb.WatchServer.ty) [] sds ∗
      ⌜sds.map (fun sd => (sd.StreamName', (#sd.Handler' : val))) =
        [(go!"Watch", @! etcdserverpb._Watch_Watch_Handler)]⌝) ∗
    v3rpc.descOk (globalAddr etcdserverpb.Lease_ServiceDesc) go!"etcdserverpb.Lease"
      etcdserverpb.LeaseServer.ty ∗
    v3rpc.descOk (globalAddr etcdserverpb.Cluster_ServiceDesc) go!"etcdserverpb.Cluster"
      etcdserverpb.ClusterServer.ty ∗
    v3rpc.descOk (globalAddr etcdserverpb.Auth_ServiceDesc) go!"etcdserverpb.Auth"
      etcdserverpb.AuthServer.ty ∗
    v3rpc.descOk (globalAddr etcdserverpb.Maintenance_ServiceDesc) go!"etcdserverpb.Maintenance"
      etcdserverpb.MaintenanceServer.ty)

instance v3rpc.svcDescsOk_persistent : Persistent (v3rpc.svcDescsOk (GF := GF)) := by
  unfold v3rpc.svcDescsOk; infer_instance

/-- **What `v3rpc.Server` and its callees read of the server** (a record; see the file header):
the server's contract (`raftKV` at `A`), its watchable store (`wsl`, `γ`, the apply thread's
environment `E`), its logger `lg` (`s.lg`), its configuration's logger `lg0` (`s.Cfg.Logger`), quota
`qb`, member id `mid`, transaction budget `n`, unary-request warning duration `wd`, cluster `c`,
`stopping` channel `ch`, tick and election settings `tm`, `et`, request size `m`, feature gate `fg`,
metrics level `mt`, distributed tracing switch `tr` and options `tos` (in the slice `tsl`), and the
`MaxConcurrentStreams` bound `mcs`. -/
structure v3rpc.GrpcCfg (GF : BundledGFunctors) [FfiSyntax] where
  A : v3rpc.KVAns GF
  E : apply.AEnv GF
  γ : mvcc.WsNames
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
read-only, as `NewServer` left them. -/
def v3rpc.grpcCfgOk (s : Loc) (C : v3rpc.GrpcCfg GF) : IProp GF :=
  iprop(v3rpc.raftKV s C.A ∗ v3rpc.watchSrvOk s C.E C.γ C.wsl ∗
    srvKVAddr s ↦□ v3rpc.wsIface C.wsl ∗ v3rpc.srvIdsOk s ∗
    srvCfgFieldAddr s go!"Logger" ↦□ C.lg0 ∗ ⌜C.lg0 ≠ null⌝ ∗ srvLgAddr s ↦□ C.lg ∗ ⌜C.lg ≠ null⌝ ∗
    srvCfgFieldAddr s go!"QuotaBackendBytes" ↦□ C.qb ∗ srvMemberIDAddr s ↦□ C.mid ∗
    srvCfgFieldAddr s go!"MaxTxnOps" ↦□ C.n ∗
    srvCfgFieldAddr s go!"WarningUnaryRequestDuration" ↦□ C.wd ∗
    srvLeadInv s ∗ srvClusterAddr s ↦□ C.c ∗ membership.isRaftCluster C.c ∗
    membership.localKept C.c ∗ srvStoppingAddr s ↦□ C.ch ∗ stopChan C.ch ∗
    cfgTickMsAddr (srvCfgAddr s) ↦□ C.tm ∗ cfgElectionTicksAddr (srvCfgAddr s) ↦□ C.et ∗
    srvCfgFieldAddr s go!"MaxRequestBytes" ↦□ C.m ∗
    srvCfgFieldAddr s go!"ServerFeatureGate" ↦□ C.fg ∗ isFeatureGate C.fg ∗
    srvCfgFieldAddr s go!"Metrics" ↦□ C.mt ∗
    srvCfgFieldAddr s go!"EnableDistributedTracing" ↦□ C.tr ∗
    srvCfgFieldAddr s go!"TracerOptions" ↦□ C.tsl ∗ C.tsl ↦*□ C.tos ∗
    srvCfgFieldAddr s go!"MaxConcurrentStreams" ↦□ C.mcs ∗
    v3rpc.runsNoRequireLeader ∗ v3rpc.metricsVars ∗ v3rpc.svcDescsOk)

instance v3rpc.grpcCfgOk_persistent (s : Loc) (C : v3rpc.GrpcCfg GF) :
    Persistent (v3rpc.grpcCfgOk s C) := by
  unfold v3rpc.grpcCfgOk; infer_instance

end defs

end EtcdGrove
end Perennial
