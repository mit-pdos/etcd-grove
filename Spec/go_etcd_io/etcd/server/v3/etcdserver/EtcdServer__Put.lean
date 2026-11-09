/-
## `(*EtcdServer).Put(ctx, r)`

**Users.** The gRPC KV handler (`api/v3rpc/key.go:95`, `kvServer.Put` through `RaftKV`: the request
validated by `checkPutRequest`, the context grpc's incoming one with its auth metadata), the
grpc-proxy's adapter. Snippet: `examples/specreq/etcdserverreq/kv.go` (`ReqPutThenRange`,
`ReqRefusalNotApplied`).

**Proof sketch.** `traceutil.Tracer.Start` (otel's span, 4b's boundary), `context.WithValue`
(W0's `Context.WithValue.spec`), `raftRequest(ctx, &pb.InternalRaftRequest{Put: r})`
(`raftRequest.spec` at `ir = .req (.put pr)`, the message wrapped by 3h's law, `irrOwn r' dq ir`,
given back and unwrapped: `putReqOwn r dq pr` returns; `IrrBody.wf` from the premise), the caller's
update passed on; on `nil`, the type assertion `resp.(*pb.PutResponse)`: `irrReply`'s dynamic type
is `respTy (.put pr)`, so it never panics, and its message is `putReply`'s.
The premise `pr.invalid = none` is `checkPutRequest`'s (2a's handler establishes it): the server
does not check it and would apply an empty key or an `IgnoreValue` put with a value, which W0's model
answers with the gRPC layer's error (round 1, provability F5).

**Changes.** The old spec (`specs-ref`'s `EtcdServer__Put.lean`; the approved candidate of
`.claude/skills/spec/examples/put.md`: `isKVServer s γ`, `kvState`, `kvOpStep`) restated over W0's
cluster state and `Step`: leases (`op.leaseID = 0` dropped), auth (the principal `reqPrin`), every
error of the model (an `IgnoreValue` put of a missing key: `ErrKeyNotFound`, fired), and the three
outcomes (the update given back for a request never applied: a stale auth revision, too many
requests). The handle is 2e's `isServer`.

**Margin.** The reply's header fields other than the revision are not stated (2a's `fill` overwrites
them). An unsettled call's update may still fire (inside the cluster's invariant): the caller learns
nothing of it.
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

/-- **`s.Put(ctx, r)`**: the put `p`, proposed through raft; its update fired at most once, at its entry's commit, with the answer the apply computes (or given back, or unsettled). -/
def EtcdServer.Put.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster) (ctx : GoInterface) (p tls : Principal) (r : Loc) (dq : DFrac) (pr : PutReq),
  SrvCallTriple (App (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!! go!"Put")) (Val #ctx)) (Val #r))
    iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isServer s γ ∗
        Context.ctxOk ctx ∗ reqPrin ctx p tls ∗ threadTok ∗ putReqOwn r dq pr ∗ ⌜pr.invalid = none⌝)
    iprop(threadTok ∗ putReqOwn r dq pr) γ p tls (.put pr) false (ClientV3.putReply)

end spec
end EtcdServer
end EtcdGrove
end Perennial
