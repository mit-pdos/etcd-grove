/-
`(*maintenanceClient).Snapshot` (`api/etcdserverpb/rpc_grpc.pb.go`, generated): the server-streaming stub.

Users: the client's `maintenance.Snapshot` (`client/v3/maintenance.go`), through `remoteMaintAt`.
Proof sketch: `StaticMethod()`, `append`, the stream descriptor `&Maintenance_ServiceDesc.Streams[0]`
(the caller's `sd`), the connection's `NewStream` (the caller's `serverStreamStubWP`), the wrapper
`&grpc.GenericClientStream[...]{ClientStream: stream}` (persisted: grpc's `genCliAt`, its intended
realization), then `x.ClientStream.SendMsg(in)` and `x.ClientStream.CloseSend()`, each error
returned with a `nil` stream. Blocked: the body is untranslated (names only in `Code/go_etcd_io/etcd/api/v3/etcdserverpb.toml`): the proof waits for its translation (open question 7.4).
Changes: verify-round: new (A6 completeness F1), in the form of the translated streaming stubs
(`leaseClient.LeaseKeepAlive.spec`); the wrapper is grpc's `genCliAt` (its message types have no
translated Lean type to state the wrapper's points-to at).
Margin: none.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.api.v3.etcdserverpb.StreamShapes

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace EtcdServerPb

open Iris Iris.BI EtcdModel EtcdWire
open go_etcd_io.etcd.api.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.api.v3.etcdserverpb.Assumptions]

/-- `c.Snapshot(ctx, in, opts...)`: the connection's `NewStream` of `/etcdserverpb.Maintenance/Snapshot`, the request
sent and the sending half closed (WP form). -/
def maintenanceClient.Snapshot.spec : Prop :=
  ∀ (c : Loc) (cc ctx : GoInterface) (q : Loc) (opts : GoSlice) (dq : DFrac) (os : List GoInterface)
    (Ψ : val → IProp GF),
  isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗ stubAt etcdserverpb.maintenanceClient c cc ∗ opts ↦*{dq} os ∗
    (∀ sd : Loc, opts ↦*{dq} os -∗
      serverStreamStubWP cc sd etcdserverpb.Maintenance_Snapshot_FullMethodName etcdserverpb.SnapshotRequest.ty etcdserverpb.SnapshotResponse.ty
        ctx q os Ψ) ⊢
  WP (App (App (App (Val (c @!! go.GoType.PointerType etcdserverpb.maintenanceClient.ty @!! go!"Snapshot")) (Val #ctx)) (Val #q))
    (Val #opts)) {{ Ψ }}

end spec

end EtcdServerPb
end EtcdGrove
end Perennial
