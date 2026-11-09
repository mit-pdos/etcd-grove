/-
`kvServer.Put` (`server/etcdserver/api/v3rpc/`).

Users: grpc's run of `/etcdserverpb.KV/Put` (the generated `_KV_Put_Handler`, 3h,
registered by `v3rpc.Server`); W0's `RemoteKV.*Triple` through grpc and the stub (`examples/specreq/clientv3kv/`, `examples/specreq/v3rpc/kv.go`).

Proof sketch: the run's request (`msgAt`, owned) is decoded to the model's request (3h's law relating `reqModels` to W0's `putReqOwn`); the gRPC check (`checkPutRequest.spec`): an error is a validation answer of the model (`kvStep`'s ``PutReq.invalid`` disjunct, at any state), so the handler fires the caller's update itself with it, `σ' = σ` (the contract's first way: `Q` with `ansOutcome`'s status `desc e`, `rpctypes`' `ErrGRPC*`: `Rpctypes.init.spec`); then `s.kv.Put(ctx, r)` (2c's `EtcdServer.Put.spec`, a `SrvCallTriple` over `isServer s γ`, the principal `EtcdServer.reqPrin ctx who` from the run's `rpcCtx ctx md` and the contract's `mdPrin γ md who` (a law of 2c/3d), the update passed on): outcome 1 gives `Q` and the reply (`srvReply`: W0's `putReply` message, or a server error `srvErrOf err e`), outcome 2 gives the update back with an unfired error (the contract's second way when it is a token refusal, else the third: `srvUnfired` errors are refusals or indefinite, so a refusal is fired by the handler as `Step.refuse`), outcome 3 the third way; `togRPCError` (`togRPCError.spec`: `ErrGRPC*` of `e`, `sentStatus` with `desc e`); `hdr.fill(resp.Header)` (`header.fill.spec`: the ids, term and leader, the revision kept: a reply's revision is at least `1`), the reply's content then models the same body (`replyModels` ignores the ids).

Changes: from `specs-ref/Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/kvServer__Put.lean`: the contract's three ways (was `putCheck`/`kvOut` over `KVAns`); a lease, `IgnoreValue`/`IgnoreLease`, auth on.

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

/-- `kvServer.Put(ctx, r)` meets the contract of `/etcdserverpb.KV/Put`. -/
def kvServer.Put.spec : Prop :=
  ∀ (p s : Loc) (γ : Cluster) (ep : GoString),
  HandlerTriple (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty @!! go!"Put")
    iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ kvServerAt p s γ) (etcdUnary γ ep go!"/etcdserverpb.KV/Put") go_etcd_io.etcd.api.v3.etcdserverpb.PutRequest.ty go_etcd_io.etcd.api.v3.etcdserverpb.PutResponse.ty

end spec

end V3rpc
end EtcdGrove
end Perennial
