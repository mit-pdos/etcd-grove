/-
`maintenanceServer.MoveLeader` (`server/etcdserver/api/v3rpc/`).

Users: grpc's run of `/etcdserverpb.Maintenance/MoveLeader` (the generated `_Maintenance_MoveLeader_Handler`, 3h,
registered by `v3rpc.Server`); `authMaintenanceServer`'s method (this batch), the registered value's.

Proof sketch: the leader check, `ms.lt.MoveLeader(...)` (2d's transfer: no modelled state): any outcome.

Changes: new (the inner method; the old specs were of the wrapper's: `specs-ref/Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/authMaintenanceServer__MoveLeader.lean`).

Margin: none.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace V3rpc

open Iris Iris.BI EtcdModel EtcdWire ClientV3 Grpc Proto EtcdServer

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `maintenanceServer.MoveLeader(ctx, r)` meets the contract of `/etcdserverpb.Maintenance/MoveLeader`. -/
def maintenanceServer.MoveLeader.spec : Prop :=
  ∀ (p s : Loc) (γ : Cluster),
  HandlerTriple (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.maintenanceServer.ty @!! go!"MoveLeader")
    iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ maintAt p s γ) (etcdLocal) go_etcd_io.etcd.api.v3.etcdserverpb.MoveLeaderRequest.ty go_etcd_io.etcd.api.v3.etcdserverpb.MoveLeaderResponse.ty

end spec

end V3rpc
end EtcdGrove
end Perennial
