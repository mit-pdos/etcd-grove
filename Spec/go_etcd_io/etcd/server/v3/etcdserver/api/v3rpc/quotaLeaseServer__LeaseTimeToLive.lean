/-
`quotaLeaseServer.LeaseTimeToLive` (`server/etcdserver/api/v3rpc/`).

Users: grpc's run of `/etcdserverpb.Lease/LeaseTimeToLive` (the generated `_Lease_LeaseTimeToLive_Handler`, 3h,
registered by `v3rpc.Server`); 1c's `RemoteCallTriple` for the lease RPCs through grpc and the stub (`examples/specreq/clientv3lease/`, `examples/specreq/v3rpc/lease.go`).

Proof sketch: the promoted method of the embedded `LeaseServer` (`LeaseServer.LeaseTimeToLive.spec`).

Changes: new (the promoted method grpc calls on the registered value).

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

/-- `quotaLeaseServer.LeaseTimeToLive(ctx, r)` meets the contract of `/etcdserverpb.Lease/LeaseTimeToLive`. -/
def quotaLeaseServer.LeaseTimeToLive.spec : Prop :=
  ∀ (p : Loc) (ls : GoInterface) (s : Loc) (γ : Cluster),
  HandlerTriple (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaLeaseServer.ty @!! go!"LeaseTimeToLive")
    iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ quotaLeaseAt p ls s γ) (etcdUnary γ go!"/etcdserverpb.Lease/LeaseTimeToLive") go_etcd_io.etcd.api.v3.etcdserverpb.LeaseTimeToLiveRequest.ty go_etcd_io.etcd.api.v3.etcdserverpb.LeaseTimeToLiveResponse.ty

end spec

end V3rpc
end EtcdGrove
end Perennial
