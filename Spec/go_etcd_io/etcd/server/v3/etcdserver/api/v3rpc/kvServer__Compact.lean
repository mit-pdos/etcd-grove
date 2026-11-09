/-
`kvServer.Compact` (`server/etcdserver/api/v3rpc/`).

Users: grpc's run of `/etcdserverpb.KV/Compact` (the generated `_KV_Compact_Handler`, 3h,
registered by `v3rpc.Server`); W0's `RemoteKV.*Triple` through grpc and the stub (`examples/specreq/clientv3kv/`, `examples/specreq/v3rpc/kv.go`). The compactor's `Compact` (2e) calls the server directly, not this handler.

Proof sketch: the run's request (`msgAt`, owned) is decoded to the model's request (3h's law relating `reqModels` to W0's `compactReqOwn`); `aa.isPermitted(ctx)` (`AuthAdmin.isPermitted.spec`): an error is the admin refusal `adminErr`-like `e` at the member's local auth state, fired by the handler as the answer (**W0's `kvStep` for `.compact` has no such answer: `req/go_etcd_io_etcd_api_v3.md`, from 2a**); then `s.kv.Compact(ctx, r)` (2c's `EtcdServer.Compact.spec`, a `SrvCallTriple` over `isServer s γ`, the principal `EtcdServer.reqPrin ctx who` from the run's `rpcCtx ctx md` and the contract's `mdPrin γ md who` (a law of 2c/3d), the update passed on): outcome 1 gives `Q` and the reply (`srvReply`: W0's `compactReply` message, or a server error `srvErrOf err e`), outcome 2 gives the update back with an unfired error (the contract's second way when it is a token refusal, else the third: `srvUnfired` errors are refusals or indefinite, so a refusal is fired by the handler as `Step.refuse`), outcome 3 the third way; `togRPCError` (`togRPCError.spec`: `ErrGRPC*` of `e`, `sentStatus` with `desc e`); `hdr.fill(resp.Header)` (`header.fill.spec`: the ids, term and leader, the revision kept: a reply's revision is at least `1`), the reply's content then models the same body (`replyModels` ignores the ids).

Changes: from `specs-ref/Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/kvServer__Compact.lean`: auth on (the admin check), physical compactions.

Round 1: the contract is the member's at `ep` (`etcdContract γ ep`; the lease requests' `leaseFact`); the first way fires no token or learner refusal (`firedAns`: 2c returns an apply-time `ErrUserEmpty`/`ErrAuthOldRevision`/`ErrInvalidAuthToken` unfired, its outcome 2, which this handler sends by the second way); errors reach `togRPCError` with 2c's `srvErrOk`; a read composes with 2c's `SrvCallTriple` once W0's round 4 makes `srvStep` `Step` (a read's permission checked at an auth state between the call's start and its answer).

Margin: the code checks the admin role at the member's possibly stale auth state; the spec relies on the model answering `adminErr` at any state.
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

/-- `kvServer.Compact(ctx, r)` meets the contract of `/etcdserverpb.KV/Compact`. -/
def kvServer.Compact.spec : Prop :=
  ∀ (p s : Loc) (γ : Cluster) (ep : GoString),
  HandlerTriple (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty @!! go!"Compact")
    iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ kvServerAt p s γ) (etcdUnary γ ep go!"/etcdserverpb.KV/Compact") go_etcd_io.etcd.api.v3.etcdserverpb.CompactionRequest.ty go_etcd_io.etcd.api.v3.etcdserverpb.CompactionResponse.ty

end spec

end V3rpc
end EtcdGrove
end Perennial
