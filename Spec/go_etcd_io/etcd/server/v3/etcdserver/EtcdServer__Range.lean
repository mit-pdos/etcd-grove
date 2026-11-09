/-
## `(*EtcdServer).Range(ctx, r)`

**Users.** The gRPC KV handler (`api/v3rpc/key.go:53`, after `checkRangeRequest`: a non-empty key, a
valid sort), the grpc-proxy's adapter, the corruption checker's and the cluster version's reads
(through the client). Snippets: `examples/specreq/etcdserverreq/kv.go` (`ReqPutThenRange`,
`ReqSerializableRange`).

**Proof sketch.** At the call, a ghost step registers the caller's persistent update in the
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
permission: with auth enabled at `kp`, the token's revision equal at the end means the auth state
did not change in between, so the check holds at `kr`; with auth disabled at `kp` and enabled at
`kr`, it is `srvStep`'s race disjunct. A serializable read skips the read index and is answered at
the member's view (`KVHist.IsView`), fired at the cluster's current state.

**Changes.** The old spec (`specs-ref`'s `EtcdServer__Range.lean`; the approved candidate of
`.claude/skills/spec/examples/range.md`: `□ AU` over `kvState`, `σr.PastOf σ`, a trace context)
restated over W0's state and `Step` (whose serializable case is the old `PastOf`), with auth
(`reqPrin`, the permission at the state read, the race disjunct), compaction and future revisions
(fired errors), and the three outcomes. The trace context premises went: `EnsureTrace` makes one.
Premises kept: a non-empty key and a valid sort (`checkRangeRequest`'s; the model answers those with
the gRPC layer's errors, which the server does not compute).

**Margin.** A linearizable read is answered at a state at or after the read index, which may be
behind the cluster's latest (the model's linearization point is the moment the cluster was in it,
inside the call). The `AuthEnable` race disjunct is the code's; see `ApiReq.lean`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiReq

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
  ∀ (s : Loc) (γ : Cluster) (ctx : GoInterface) (who : Principal) (r : Loc) (dq : DFrac) (rm : RangeReq),
  SrvCallTriple (App (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!! go!"Range")) (Val #ctx)) (Val #r))
    iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isServer s γ ∗
        Context.ctxOk ctx ∗ reqPrin ctx who ∗ threadTok ∗ rangeReqOwn r dq rm ∗ ⌜rm.key ≠ [] ∧ rm.validSort⌝)
    iprop(threadTok ∗ rangeReqOwn r dq rm) γ who (.range rm) true (ClientV3.getReply)

end spec
end EtcdServer
end EtcdGrove
end Perennial
