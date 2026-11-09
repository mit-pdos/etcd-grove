/-
`maintenanceServer.Downgrade` (`server/etcdserver/api/v3rpc/`).

Users: grpc's run of `/etcdserverpb.Maintenance/Downgrade` (the generated `_Maintenance_Downgrade_Handler`, 3h,
registered by `v3rpc.Server`); `authMaintenanceServer`'s method (this batch), the registered value's.

Proof sketch: `ms.d.Downgrade(ctx, r)` (2e: the cluster version, not modelled): any outcome.

Changes: new (the inner method; the old specs were of the wrapper's: `specs-ref/Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/authMaintenanceServer__Downgrade.lean`).

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

/-- `maintenanceServer.Downgrade(ctx, r)` meets the contract of `/etcdserverpb.Maintenance/Downgrade`. -/
def maintenanceServer.Downgrade.spec : Prop :=
  ∀ (p s : Loc) (γ : Cluster),
  HandlerTriple (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.maintenanceServer.ty @!! go!"Downgrade")
    iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ maintAt p s γ) (etcdLocal) go_etcd_io.etcd.api.v3.etcdserverpb.DowngradeRequest.ty go_etcd_io.etcd.api.v3.etcdserverpb.DowngradeResponse.ty

end spec

end V3rpc
end EtcdGrove
end Perennial
