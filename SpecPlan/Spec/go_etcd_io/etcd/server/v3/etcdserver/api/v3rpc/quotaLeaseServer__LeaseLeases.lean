/-
`quotaLeaseServer.LeaseLeases` (`server/etcdserver/api/v3rpc/`).

Users: grpc's run of `/etcdserverpb.Lease/LeaseLeases` (the generated `_Lease_LeaseLeases_Handler`, 3h,
registered by `v3rpc.Server`); 1c's `RemoteCallTriple` for the lease RPCs through grpc and the stub (`examples/specreq/clientv3lease/`, `examples/specreq/v3rpc/lease.go`).

Proof sketch: the promoted method of the embedded `LeaseServer` (`LeaseServer.LeaseLeases.spec`).

Changes: new (the promoted method grpc calls on the registered value).

Round 1: the contract is the member's at `ep` (`etcdContract γ ep`; the lease requests' `leaseFact`); the first way fires no token or learner refusal (`firedAns`: 2c returns an apply-time `ErrUserEmpty`/`ErrAuthOldRevision`/`ErrInvalidAuthToken` unfired, its outcome 2, which this handler sends by the second way); errors reach `togRPCError` with 2c's `srvErrOk`; a read composes with 2c's `SrvCallTriple` (W0's `lo`, rounds 4-6; integration I3: the Api header's "Composition with 2c").

Changes: verify-round relay (server-core's RR request 1): takes `srvAt s γ ep`, passed to `LeaseServer`'s.

Margin: none.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Api

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

/-- `quotaLeaseServer.LeaseLeases(ctx, r)` meets the contract of `/etcdserverpb.Lease/LeaseLeases`. -/
def quotaLeaseServer.LeaseLeases.spec : Prop :=
  ∀ (p : Loc) (ls : GoInterface) (s : Loc) (γ : Cluster) (ep : GoString) (gq : Qp),
  HandlerTriple (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaLeaseServer.ty @!! go!"LeaseLeases")
    iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ quotaLeaseAt p ls s γ ∗ srvAt s γ ep) (etcdUnary γ ep go!"/etcdserverpb.Lease/LeaseLeases") go_etcd_io.etcd.api.v3.etcdserverpb.LeaseLeasesRequest.ty go_etcd_io.etcd.api.v3.etcdserverpb.LeaseLeasesResponse.ty (srvGate s gq)

end spec

end V3rpc
end EtcdGrove
end Perennial
