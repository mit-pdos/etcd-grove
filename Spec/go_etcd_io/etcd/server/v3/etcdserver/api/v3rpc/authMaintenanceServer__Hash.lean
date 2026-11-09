/-
`authMaintenanceServer.Hash` (`server/etcdserver/api/v3rpc/`).

Users: grpc's run of `/etcdserverpb.Maintenance/Hash` (the generated `_Maintenance_Hash_Handler`, 3h,
registered by `v3rpc.Server`); 1c's `Maint.methods` through grpc (`examples/specreq/clientv3client/maint.go`).

Proof sketch: `ams.isPermitted(ctx)` (an error: any outcome is allowed); then `maintenanceServer.Hash.spec` of the embedded value.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/authMaintenanceServer__Hash.lean`: over the contract.

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

/-- `authMaintenanceServer.Hash(ctx, r)` meets the contract of `/etcdserverpb.Maintenance/Hash`. -/
def authMaintenanceServer.Hash.spec : Prop :=
  ∀ (p s : Loc) (γ : Cluster),
  HandlerTriple (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.authMaintenanceServer.ty @!! go!"Hash")
    iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ authMaintAt p s γ) (etcdLocal) go_etcd_io.etcd.api.v3.etcdserverpb.HashRequest.ty go_etcd_io.etcd.api.v3.etcdserverpb.HashResponse.ty

end spec

end V3rpc
end EtcdGrove
end Perennial
