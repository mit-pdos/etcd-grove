/-
`LeaseServer.LeaseLeases` (`server/etcdserver/api/v3rpc/`).

Users: grpc's run of `/etcdserverpb.Lease/LeaseLeases` (the generated `_Lease_LeaseLeases_Handler`, 3h,
registered by `v3rpc.Server`); 1c's `RemoteCallTriple` for the lease RPCs through grpc and the stub (`examples/specreq/clientv3lease/`, `examples/specreq/v3rpc/lease.go`).

Proof sketch: `ls.le.LeaseLeases(ctx, r)` (2c's `EtcdServer.LeaseLeases.spec` at `srvAt s γ ep`, the contract's bound `vi` passed as `srvLeaseLbOpt γ ep vi` and 2c's `srvLeaseFact` given back as the contract's `leaseFact` (the same definition), the update passed on, the principal `reqPrin ctx who tls` from the contract's `mdPrin` (`reqPrin_of_md`)); `ErrLeaseNotFound` (never an answer of the model's `leaseLeases`; an unfired outcome of 2c if any) becomes an empty list, a status that settles nothing is not needed. errors through `togRPCError`; `hdr.fill`.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/LeaseServer__LeaseLeases.lean`: over the contract (was the lease rows' `leaseServerAt` with its own answers).
verify-round (A6 F1, with server-core's fix): 2c's success reply is `srvHdrReply` (`replyHdrOwn`): `replyHdrOwn_header` gives the `Header` field and a non-`nil` header for `hdr.fill` (`header.fill.spec`), `replyHdrOwn_replyOwn` the reply back.

Round 1: the contract is the member's at `ep` (`etcdContract γ ep`; the lease requests' `leaseFact`); the first way fires no token or learner refusal (`firedAns`: 2c returns an apply-time `ErrUserEmpty`/`ErrAuthOldRevision`/`ErrInvalidAuthToken` unfired, its outcome 2, which this handler sends by the second way); errors reach `togRPCError` with 2c's `srvErrOk`; a read composes with 2c's `SrvCallTriple` (W0's `lo`, rounds 4-6; integration I3: the Api header's "Composition with 2c").

Changes: verify-round relay (server-core's RR request 1): takes `srvAt s γ ep` (2c's lease specs do: the lease view is the member's at the endpoint it serves); `leaseFact` is 2c's `srvLeaseFact`.

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

/-- `LeaseServer.LeaseLeases(ctx, r)` meets the contract of `/etcdserverpb.Lease/LeaseLeases`. -/
def LeaseServer.LeaseLeases.spec : Prop :=
  ∀ (p s : Loc) (γ : Cluster) (ep : GoString) (gq : Qp),
  HandlerTriple (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.LeaseServer.ty @!! go!"LeaseLeases")
    iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ leaseServerAt p s γ ∗ srvAt s γ ep) (etcdUnary γ ep go!"/etcdserverpb.Lease/LeaseLeases") go_etcd_io.etcd.api.v3.etcdserverpb.LeaseLeasesRequest.ty go_etcd_io.etcd.api.v3.etcdserverpb.LeaseLeasesResponse.ty (srvGate s gq)

end spec

end V3rpc
end EtcdGrove
end Perennial
