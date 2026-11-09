/-
`maintenanceServer.Defragment` (`server/etcdserver/api/v3rpc/`).

Users: grpc's run of `/etcdserverpb.Maintenance/Defragment` (the generated `_Maintenance_Defragment_Handler`, 3h,
registered by `v3rpc.Server`); `authMaintenanceServer`'s method (this batch), the registered value's.

Proof sketch: the health notifier (`notifierAt`), `ms.defrag.Defragment()` (4a's backend: no modelled state changes), the header: any outcome.

Changes: new (the inner method; the old specs were of the wrapper's: `specs-ref/Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/authMaintenanceServer__Defragment.lean`).

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

/-- `maintenanceServer.Defragment(ctx, r)` meets the contract of `/etcdserverpb.Maintenance/Defragment`. -/
def maintenanceServer.Defragment.spec : Prop :=
  ∀ (p s : Loc) (γ : Cluster),
  HandlerTriple (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.maintenanceServer.ty @!! go!"Defragment")
    iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ maintAt p s γ) (etcdLocal) go_etcd_io.etcd.api.v3.etcdserverpb.DefragmentRequest.ty go_etcd_io.etcd.api.v3.etcdserverpb.DefragmentResponse.ty

end spec

end V3rpc
end EtcdGrove
end Perennial
