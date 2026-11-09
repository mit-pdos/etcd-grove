/-
`kvServer.DeleteRange` (`server/etcdserver/api/v3rpc/`).

Users: grpc's run of `/etcdserverpb.KV/DeleteRange` (the generated `_KV_DeleteRange_Handler`, 3h,
registered by `v3rpc.Server`); W0's `RemoteKV.*Triple` through grpc and the stub (`examples/specreq/clientv3kv/`, `examples/specreq/v3rpc/kv.go`).

Proof sketch: the run's request (`msgAt`, owned) is decoded to the model's request (3h's law relating `reqModels` to W0's `deleteReqOwn`); the gRPC check (`checkDeleteRequest.spec`): an error is a validation answer of the model (`kvStep`'s `emptyKey` disjunct, at any state), so the handler fires the caller's update itself with it, `σ' = σ` (the contract's first way: `Q` with `ansOutcome`'s status `desc e`, `rpctypes`' `ErrGRPC*`: `Rpctypes.init.spec`); then `s.kv.DeleteRange(ctx, r)` (2c's `EtcdServer.DeleteRange.spec`, a `SrvCallTriple` over `isServer s γ`, the principal `EtcdServer.reqPrin ctx who tls` from the run's `rpcCtx ctx md` and the contract's `mdPrin γ md who` (`reqPrin_of_md`), the caller's `authLb γ lo` and the update converted to one over `srvStep who tls rq … lo` (the Api header's "Composition with 2c")): outcome 1 gives `Q` and the reply (`srvReply`: W0's `deleteReply` message, or a server error `srvErr err e`), outcome 2 gives the update back with an unfired error (the contract's second way when it is a token refusal, else the third: `srvUnfired` errors are refusals or indefinite, so a refusal is fired by the handler as `Step.refuse`), outcome 3 the third way; `togRPCError` (`togRPCError.spec`: `ErrGRPC*` of `e`, `sentStatus` with `desc e`); `hdr.fill(resp.Header)` (`header.fill.spec`: the ids, term and leader, the revision kept: a reply's revision is at least `1`), the reply's content then models the same body (`replyModels` ignores the ids).

Changes: from `specs-ref/Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/kvServer__DeleteRange.lean`: as `Put`.
verify-round (A6 F6): the reply's depth (≤ 2) from 3h's `holds_depth_resp`.

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

/-- `kvServer.DeleteRange(ctx, r)` meets the contract of `/etcdserverpb.KV/DeleteRange`. -/
def kvServer.DeleteRange.spec : Prop :=
  ∀ (p s : Loc) (γ : Cluster) (ep : GoString) (gq : Qp),
  HandlerTriple (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty @!! go!"DeleteRange")
    iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ kvServerAt p s γ) (etcdUnary γ ep go!"/etcdserverpb.KV/DeleteRange") go_etcd_io.etcd.api.v3.etcdserverpb.DeleteRangeRequest.ty go_etcd_io.etcd.api.v3.etcdserverpb.DeleteRangeResponse.ty (srvGate s gq)

end spec

end V3rpc
end EtcdGrove
end Perennial
