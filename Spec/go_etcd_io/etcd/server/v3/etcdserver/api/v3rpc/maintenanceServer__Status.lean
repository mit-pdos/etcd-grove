/-
`maintenanceServer.Status` (`server/etcdserver/api/v3rpc/`).

Users: grpc's run of `/etcdserverpb.Maintenance/Status` (the generated `_Maintenance_Status_Handler`, 3h,
registered by `v3rpc.Server`); `authMaintenanceServer`'s method (this batch), the registered value's.

Proof sketch: reads the member's raft status, backend sizes, configuration, versions and alarms (2d/2e's getters, read-only), builds a fresh reply: any outcome is allowed (`etcdLocal`).

Changes: new (the inner method; the old specs were of the wrapper's: `specs-ref/Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/authMaintenanceServer__Status.lean`).

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

/-- `maintenanceServer.Status(ctx, r)` meets the contract of `/etcdserverpb.Maintenance/Status`. -/
def maintenanceServer.Status.spec : Prop :=
  ∀ (p s : Loc) (γ : Cluster),
  HandlerTriple (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.maintenanceServer.ty @!! go!"Status")
    iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ maintAt p s γ) (etcdLocal) go_etcd_io.etcd.api.v3.etcdserverpb.StatusRequest.ty go_etcd_io.etcd.api.v3.etcdserverpb.StatusResponse.ty

end spec

end V3rpc
end EtcdGrove
end Perennial
