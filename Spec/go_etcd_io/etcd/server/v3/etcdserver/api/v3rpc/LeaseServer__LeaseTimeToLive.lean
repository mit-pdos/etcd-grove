/-
`LeaseServer.LeaseTimeToLive` (`server/etcdserver/api/v3rpc/`).

Users: grpc's run of `/etcdserverpb.Lease/LeaseTimeToLive` (the generated `_Lease_LeaseTimeToLive_Handler`, 3h,
registered by `v3rpc.Server`); 1c's `RemoteCallTriple` for the lease RPCs through grpc and the stub (`examples/specreq/clientv3lease/`, `examples/specreq/v3rpc/lease.go`).

Proof sketch: `ls.le.LeaseTimeToLive(ctx, r)` (2c's `EtcdServer.LeaseTimeToLive.spec`, the update passed on, the principal from the contract's `mdPrin`); `ErrLeaseNotFound` becomes the reply `ID`, `TTL = -1` (`ansOutcome`'s case: the update fired with `.err .leaseNotFound`). errors through `togRPCError`; `hdr.fill`.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/LeaseServer__LeaseTimeToLive.lean`: over the contract (was the lease rows' `leaseServerAt` with its own answers).

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

/-- `LeaseServer.LeaseTimeToLive(ctx, r)` meets the contract of `/etcdserverpb.Lease/LeaseTimeToLive`. -/
def LeaseServer.LeaseTimeToLive.spec : Prop :=
  ∀ (p s : Loc) (γ : Cluster) (ep : GoString),
  HandlerTriple (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.LeaseServer.ty @!! go!"LeaseTimeToLive")
    iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ leaseServerAt p s γ) (etcdUnary γ ep go!"/etcdserverpb.Lease/LeaseTimeToLive") go_etcd_io.etcd.api.v3.etcdserverpb.LeaseTimeToLiveRequest.ty go_etcd_io.etcd.api.v3.etcdserverpb.LeaseTimeToLiveResponse.ty

end spec

end V3rpc
end EtcdGrove
end Perennial
