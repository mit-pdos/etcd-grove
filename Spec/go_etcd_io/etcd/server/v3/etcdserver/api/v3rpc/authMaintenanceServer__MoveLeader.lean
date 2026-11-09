/-
`authMaintenanceServer.MoveLeader` (`server/etcdserver/api/v3rpc/`).

Users: grpc's run of `/etcdserverpb.Maintenance/MoveLeader` (the generated `_Maintenance_MoveLeader_Handler`, 3h,
registered by `v3rpc.Server`); 1c's `Maint.methods` through grpc (`examples/specreq/clientv3client/maint.go`).

Proof sketch: `ams.isPermitted(ctx)` (an error: any outcome is allowed); then `maintenanceServer.MoveLeader.spec` of the embedded value.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/authMaintenanceServer__MoveLeader.lean`: over the contract.

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

/-- `authMaintenanceServer.MoveLeader(ctx, r)` meets the contract of `/etcdserverpb.Maintenance/MoveLeader`. -/
def authMaintenanceServer.MoveLeader.spec : Prop :=
  ∀ (p s : Loc) (γ : Cluster),
  HandlerTriple (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.authMaintenanceServer.ty @!! go!"MoveLeader")
    iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ authMaintAt p s γ) (etcdLocal) go_etcd_io.etcd.api.v3.etcdserverpb.MoveLeaderRequest.ty go_etcd_io.etcd.api.v3.etcdserverpb.MoveLeaderResponse.ty

end spec

end V3rpc
end EtcdGrove
end Perennial
