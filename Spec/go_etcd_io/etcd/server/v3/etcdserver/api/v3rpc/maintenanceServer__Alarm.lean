/-
`maintenanceServer.Alarm` (`server/etcdserver/api/v3rpc/`).

Users: grpc's run of `/etcdserverpb.Maintenance/Alarm` (the generated `_Maintenance_Alarm_Handler`, 3h,
registered by `v3rpc.Server`); `authMaintenanceServer`'s method (this batch), the registered value's.

Proof sketch: `ms.a.Alarm(ctx, ar)` (2c's `EtcdServer.Alarm.spec` over `alarmReqOwn`: `GET` is `.alarmList`, `DEACTIVATE` `.alarmDisarm`, the update passed on); errors through `togRPCError`; the header filled.

Changes: new (the inner method; the old specs were of the wrapper's: `specs-ref/Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/authMaintenanceServer__Alarm.lean`).

Round 1: the contract is the member's at `ep` (`etcdContract γ ep`; the lease requests' `leaseFact`); the first way fires no token or learner refusal (`firedAns`: 2c returns an apply-time `ErrUserEmpty`/`ErrAuthOldRevision`/`ErrInvalidAuthToken` unfired, its outcome 2, which this handler sends by the second way); errors reach `togRPCError` with 2c's `srvErrOk`; a read composes with 2c's `SrvCallTriple` (W0's `lo`, rounds 4-6; integration I3: the Api header's "Composition with 2c").

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

/-- `maintenanceServer.Alarm(ctx, r)` meets the contract of `/etcdserverpb.Maintenance/Alarm`. -/
def maintenanceServer.Alarm.spec : Prop :=
  ∀ (p s : Loc) (γ : Cluster) (ep : GoString) (gq : Qp),
  HandlerTriple (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.maintenanceServer.ty @!! go!"Alarm")
    iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ maintAt p s γ) (etcdUnary γ ep go!"/etcdserverpb.Maintenance/Alarm") go_etcd_io.etcd.api.v3.etcdserverpb.AlarmRequest.ty go_etcd_io.etcd.api.v3.etcdserverpb.AlarmResponse.ty (srvGate s gq)

end spec

end V3rpc
end EtcdGrove
end Perennial
