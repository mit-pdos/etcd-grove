/-
`authMaintenanceServer.Alarm` (`server/etcdserver/api/v3rpc/`).

Users: grpc's run of `/etcdserverpb.Maintenance/Alarm` (the generated `_Maintenance_Alarm_Handler`, 3h,
registered by `v3rpc.Server`); 1c's `Maint.methods` through grpc (`examples/specreq/clientv3client/maint.go`).

Proof sketch: `ams.requireAuthInfo(ctx)` for `GET` (an error: a refusal or `userEmpty`, fired), `ams.isPermitted(ctx)` for the rest (an admin refusal: `clusterStep`'s `alarmDisarm` allows `adminErr` at any state, fired); then `maintenanceServer.Alarm.spec` of the embedded value.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/authMaintenanceServer__Alarm.lean`: over the contract.

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

/-- `authMaintenanceServer.Alarm(ctx, r)` meets the contract of `/etcdserverpb.Maintenance/Alarm`. -/
def authMaintenanceServer.Alarm.spec : Prop :=
  ∀ (p s : Loc) (γ : Cluster),
  HandlerTriple (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.authMaintenanceServer.ty @!! go!"Alarm")
    iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ authMaintAt p s γ) (etcdUnary γ go!"/etcdserverpb.Maintenance/Alarm") go_etcd_io.etcd.api.v3.etcdserverpb.AlarmRequest.ty go_etcd_io.etcd.api.v3.etcdserverpb.AlarmResponse.ty

end spec

end V3rpc
end EtcdGrove
end Perennial
