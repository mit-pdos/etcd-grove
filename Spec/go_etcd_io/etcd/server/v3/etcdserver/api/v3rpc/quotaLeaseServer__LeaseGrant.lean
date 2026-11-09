/-
`quotaLeaseServer.LeaseGrant` (`server/etcdserver/api/v3rpc/`).

Users: grpc's run of `/etcdserverpb.Lease/LeaseGrant` (the generated `_Lease_LeaseGrant_Handler`, 3h,
registered by `v3rpc.Server`); 1c's `RemoteCallTriple` for the lease RPCs through grpc and the stub (`examples/specreq/clientv3lease/`, `examples/specreq/v3rpc/lease.go`).

Proof sketch: `qa.check` (as `quotaKVServer.Put`): `.noSpace` fired; else `LeaseServer.LeaseGrant.spec`.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/quotaLeaseServer__LeaseGrant.lean`.

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

/-- `quotaLeaseServer.LeaseGrant(ctx, r)` meets the contract of `/etcdserverpb.Lease/LeaseGrant`. -/
def quotaLeaseServer.LeaseGrant.spec : Prop :=
  ∀ (p : Loc) (ls : GoInterface) (s : Loc) (γ : Cluster),
  HandlerTriple (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaLeaseServer.ty @!! go!"LeaseGrant")
    iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ quotaLeaseAt p ls s γ) (etcdUnary γ go!"/etcdserverpb.Lease/LeaseGrant") go_etcd_io.etcd.api.v3.etcdserverpb.LeaseGrantRequest.ty go_etcd_io.etcd.api.v3.etcdserverpb.LeaseGrantResponse.ty

end spec

end V3rpc
end EtcdGrove
end Perennial
