/-
## `(*EtcdServer).Range(ctx, r)`

**Users.** The gRPC KV handler (`api/v3rpc/key.go:53`, after `checkRangeRequest`: a non-empty key, a
valid sort), the grpc-proxy's adapter, the health checks (`api/etcdhttp/health.go:224,435`: an
**empty key**, `KeysOnly`, `Limit: 1`, a `WithRoot` context; only `err` is used; their persistent
update is the server's read permission, 2e's, `req/`). Snippets:
`examples/specreq/etcdserverreq/kv.go` (`ReqPutThenRange`, `ReqSerializableRange`,
`ReqHealthRange`).

**Proof sketch.** An empty key (the health checks; with an empty range end: the single key `""`)
is read as the range of the key `""`, which no key is (W0's `etcdLb_keyNonEmpty`): an empty answer,
`srvStep`'s `emptyRangeStep` (W0's `kvStep` answers an empty key with the gRPC layer's
`ErrEmptyKey`, which the server does not compute). At the call, a ghost step registers the caller's persistent update in the
cluster's read registry (2d, `readReg_register`: the cluster's invariant fires it at every history
point from now on, with each answer the step allows there), which yields `committedLb γ.raft l0`, the
committed log at the registration. A linearizable read: `s.read.LinearizableReadNotify(ctx)`
(`Read.LinearizableReadNotify.spec` at `l0`, `isServer`'s `readAt s.read γ.raft (srvApplied s γ)`):
`nil` gives `srvApplied s γ |l|` with `opsOf l0 <+: opsOf l` (the history point `|l|` is at or after
the registration's, as states: 2d's history is a function of the operations); an error is a
`readErr`, unsettled (`readErr_indef`). Then `doSerialize(ctx, chk, get)` (`doSerialize.spec`):
`AuthInfoFromCtx` (`reqPrin`; an invalid token: a refusal, the update kept), `chk` =
`authStore.IsRangePermitted` at the auth store's state, the member's applied point `kp` (3d's
contract; a denial: fired at `histAt γ kp`, `Step`'s `permErr`), `get` = `txn.Range(ctx, lg,
s.KV(), r, true)` (3b's `Range` over the member's store, at an applied point `kr ≥ kp`: the answer
`res` is one `Step` allows at `histAt γ kr σ`, or mvcc's `ErrCompacted`/`ErrFutureRev`, `Step`'s
`revErr`), the auth revision's re-check (a change: `ErrAuthOldRevision`, a refusal, the answer
dropped). The registry's ticket at `(kr, res)` gives `Q σ σ res` (2d's `readReg_get`). The
permission: checked at the auth table of `kp`, at or after the call's `lo` (the registration's
`authLb`): W0's `deniedSince`/`permittedSince` (round 6: the check at a recorded auth state at
or after the call's bound; 3d's `checkPost`, with 2d's store-index to cluster-index link,
`req/`), not the revision re-check (an auth change bumps the revision before readers see it). A serializable read skips the read index and is answered at
the member's view (`KVHist.IsView`), fired at the cluster's current state. The deferred
`txn.WarnOfExpensiveReadOnlyRangeRequest` logs the request through 3h's `stringerAt_msg` at a share
of it (`rangeReqOwn_msgAt`), its depth premise from 3h's `holds_depth` (a range request: at most `3`).

**Integration (I4): the read slot realized.** `srvApplied s γ k` gives 2d's `srvReadAt s γ k`
(`srvApplied_read`; the names from `isServer_names`, the stores' from `srvStores_agree`). `txn.Range`
(3b) takes an atomic update over 3e's `mvccState`: 2d's `srvReadAt_mvcc` gives a persistent accessor
whose commit names a history point `kr ≥ k` with the same KV history, and `srvReader_mvcc` lends
the reader token for the call's thread token. The permission check reads 3d's store at a state
`srvReadAt_auth` links to a cluster auth table at or after `k`'s, hence at or after the call's `lo`
(W0's `permittedSince`/`deniedSince`). The call holds a share of 2e's `srvGate` throughout.

**Changes.** The old spec (`specs-ref`'s `EtcdServer__Range.lean`; the approved candidate of
`.claude/skills/spec/examples/range.md`: `□ AU` over `kvState`, `σr.PastOf σ`, a trace context)
restated over W0's state and `Step` (whose serializable case is the old `PastOf`), with auth
(`reqPrin`, the permission at the state read, the race disjunct), compaction and future revisions
(fired errors), and the three outcomes. The trace context premises went: `EnsureTrace` makes one.
Premises kept: a valid sort (`checkRangeRequest`'s), and an empty key only with an empty range end
(the health checks' form). Round 1: the non-empty key dropped (health checks); the `AuthEnable` race
disjunct dropped (W0's round 4: a read's permission is checked at an auth table at or after the
call's `lo`, `State.deniedSince`/`permittedSince` (W0's round 6), which is what `doSerialize` does); the principal
pair (`reqPrin ctx p tls`).
Integration X (superseded at the re-review, below): the scope premise `EtcdServerPb.endsDecoded` (its
range ends `nil` or non-empty, `nonissues/etcd-auth-empty-range-end-point-check.md`; I5's request;
2a's handler has it from grpc's decoder; a caller that
builds its range request, by 3h's `endsOk_range_intro`).

**Margin.** A linearizable read is answered at a state at or after the read index, which may be
behind the cluster's latest (the model's linearization point is the moment the cluster was in it,
inside the call).

Changes: verify-round (client-core's request): a permission denial is fired at W0's three-view `deniedSince` (the auth table the member checked, at or after the call's `lo`: `srvReadAt_auth`).

Changes: verify-round, second pass (grpc-v3rpc's request): `endsDecoded` is now a share of the request message with the pure `endsOk` fact; 2a's handler gets it by `endsDecoded_of_canon` (`Proto.norm c = c` of a decoded message), a builder by `endsDecoded_range_intro`.

Changes: re-review (R-A6 N2): no separate `endsDecoded` share: the request's owned predicate (W0's `rangeReqOwn`/`txnReqOwn`) already carries `endsOk` of its content (3h's `*ReqOwn_msgAt`), and a share beside full ownership asked for more than the message (`kvServer.RangeStream` writes `r.Limit`, `r.Revision`, `r.Key`). `Proto.decodedAt`, `endsDecoded_of_decoded` and `endsDecoded_range_intro` no longer exist: 3h's `endsOk_canon` and `endsOk_range_intro`.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiReq

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace EtcdServer

open Iris Iris.BI EtcdModel EtcdWire

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`s.Range(ctx, r)`**: the range `rm` (linearizable: answered at a state the member applied after the call began; serializable: at the member's view), the caller's update persistent and fired by `srvStep` (the `AuthEnable` race included). -/
def EtcdServer.Range.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster) (q : Qp) (ctx : GoInterface) (p tls : Principal) (r : Loc) (dq : DFrac) (rm : RangeReq),
  SrvCallTriple (App (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!! go!"Range")) (Val #ctx)) (Val #r))
    iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isServer s γ ∗ srvGate s q ∗
        Context.ctxOk ctx ∗ reqCtxOk ctx ∗ reqPrin ctx p tls ∗ threadTok ∗ rangeReqOwn r dq rm ∗
        ⌜rm.validSort ∧ (rm.key = [] → rm.rangeEnd = [])⌝)
    iprop(srvGate s q ∗ threadTok ∗ rangeReqOwn r dq rm) γ p tls (.range rm) true (ClientV3.getReply)

end spec
end EtcdServer
end EtcdGrove
end Perennial
