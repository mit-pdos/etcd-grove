/-
`kvServer.Compact` (`server/etcdserver/api/v3rpc/`).

Users: grpc's run of `/etcdserverpb.KV/Compact` (the generated `_KV_Compact_Handler`, 3h,
registered by `v3rpc.Server`); W0's `RemoteKV.*Triple` through grpc and the stub (`examples/specreq/clientv3kv/`, `examples/specreq/v3rpc/kv.go`). The compactor's `Compact` (2e) calls the server directly, not this handler.

Proof sketch: the run's request (`msgAt`, owned) is decoded to the model's request (3h's law relating `reqModels` to W0's `compactReqOwn`); `aa.isPermitted(ctx)` (`AuthAdmin.isPermitted.spec`): a token refusal goes back unfired (the contract's second way); a denial (`adminDenied σ who e` at a state `etcdLb γ σ` bounds, the cluster's tables only grow) is fired by the handler as W0's compact denial at the current state (verify-round, A6 F5: W0's denial is at one table, `∃ a ∈ σ.authTables, ¬ a.admin who`, while the code's check reads the flag and the user at two; requested of W0 to admit `adminDenied`'s two-table shape, as its reads' `deniedSince` does); then `s.kv.Compact(ctx, r)` (2c's `EtcdServer.Compact.spec`, a `SrvCallTriple` over `isServer s γ`, the principal `EtcdServer.reqPrin ctx who tls` from the run's `rpcCtx ctx md` and the contract's `mdPrin γ md who` (`reqPrin_of_md`), the caller's `authLb γ lo` and the update converted to one over `srvStep who tls rq … lo` (the Api header's "Composition with 2c")): outcome 1 gives `Q` and the reply (`srvReply`: W0's `compactReply` message, or a server error `srvErr err e`), outcome 2 gives the update back with an unfired error (the contract's second way when it is a token refusal, else the third: `srvUnfired` errors are refusals or indefinite, so a refusal is fired by the handler as `Step.refuse`), outcome 3 the third way; `togRPCError` (`togRPCError.spec`: `ErrGRPC*` of `e`, `sentStatus` with `desc e`); `hdr.fill(resp.Header)` (`header.fill.spec`: the ids, term and leader, the revision kept: a reply's revision is at least `1`), the reply's content then models the same body (`replyModels` ignores the ids).

Changes: from `specs-ref/Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/kvServer__Compact.lean`: auth on (the admin check), physical compactions.
verify-round (A6 F6): the reply's depth (≤ 2) from 3h's `holds_depth_resp`; (A6 F5) the denial from `AuthAdmin.isPermitted`'s `adminDenied`.

Round 1: the contract is the member's at `ep` (`etcdContract γ ep`; the lease requests' `leaseFact`); the first way fires no token or learner refusal (`firedAns`: 2c returns an apply-time `ErrUserEmpty`/`ErrAuthOldRevision`/`ErrInvalidAuthToken` unfired, its outcome 2, which this handler sends by the second way); errors reach `togRPCError` with 2c's `srvErrOk`; a read composes with 2c's `SrvCallTriple` (W0's `lo`, rounds 4-6; integration I3: the Api header's "Composition with 2c").

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
  ∀ (p s : Loc) (γ : Cluster) (ep : GoString) (gq : Qp),
  HandlerTriple (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty @!! go!"Compact")
    iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ kvServerAt p s γ) (etcdUnary γ ep go!"/etcdserverpb.KV/Compact") go_etcd_io.etcd.api.v3.etcdserverpb.CompactionRequest.ty go_etcd_io.etcd.api.v3.etcdserverpb.CompactionResponse.ty (srvGate s gq)

end spec

end V3rpc
end EtcdGrove
end Perennial
