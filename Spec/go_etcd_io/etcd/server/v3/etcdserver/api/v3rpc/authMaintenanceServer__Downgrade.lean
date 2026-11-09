/-
`authMaintenanceServer.Downgrade` (`server/etcdserver/api/v3rpc/`).

Users: grpc's run of `/etcdserverpb.Maintenance/Downgrade` (the generated `_Maintenance_Downgrade_Handler`, 3h,
registered by `v3rpc.Server`); 1c's `Maint.methods` through grpc (`examples/specreq/clientv3client/maint.go`).

Proof sketch: `ams.isPermitted(ctx)` (an error: any outcome is allowed); then `maintenanceServer.Downgrade.spec` of the embedded value.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/authMaintenanceServer__Downgrade.lean`: over the contract.

Round 1: the contract is the member's at `ep` (`etcdContract γ ep`; the lease requests' `leaseFact`); the first way fires no token or learner refusal (`firedAns`: 2c returns an apply-time `ErrUserEmpty`/`ErrAuthOldRevision`/`ErrInvalidAuthToken` unfired, its outcome 2, which this handler sends by the second way); errors reach `togRPCError` with 2c's `srvErrOk`; a read composes with 2c's `SrvCallTriple` once W0's round 4 makes `srvStep` `Step` (a read's permission checked at an auth state between the call's start and its answer).

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

/-- `authMaintenanceServer.Downgrade(ctx, r)` meets the contract of `/etcdserverpb.Maintenance/Downgrade`. -/
def authMaintenanceServer.Downgrade.spec : Prop :=
  ∀ (p s : Loc) (γ : Cluster) (ep : GoString),
  HandlerTriple (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.authMaintenanceServer.ty @!! go!"Downgrade")
    iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ authMaintAt p s γ) (etcdLocal) go_etcd_io.etcd.api.v3.etcdserverpb.DowngradeRequest.ty go_etcd_io.etcd.api.v3.etcdserverpb.DowngradeResponse.ty

end spec

end V3rpc
end EtcdGrove
end Perennial
