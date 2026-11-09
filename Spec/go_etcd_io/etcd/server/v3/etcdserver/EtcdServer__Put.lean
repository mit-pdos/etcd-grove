/-
## `(*EtcdServer).Put(ctx, r)`

**Users.** The gRPC KV handler (`api/v3rpc/key.go:95`, `kvServer.Put` through `RaftKV`: the request
validated by `checkPutRequest`, the context grpc's incoming one with its auth metadata), the
grpc-proxy's adapter. Snippet: `examples/specreq/etcdserverreq/kv.go` (`ReqPutThenRange`,
`ReqPutTypeAssert`).

**Proof sketch.** `traceutil.Tracer.Start` (otel's span, 4b's boundary), `context.WithValue`
(W0's `Context.WithValue.spec`), `raftRequest(ctx, &pb.InternalRaftRequest{Put: r})`
(`raftRequest.spec` at `ir = .req (.put p)`, the message built from `r`, `irrOwn`), the caller's
update passed on; on `nil`, the type assertion `resp.(*pb.PutResponse)`: `irrReply`'s dynamic type
is `respTy (.put p)`, so it never panics, and its message is `putReply`'s.

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
  ∀ (s : Loc) (γ : Cluster) (ctx : GoInterface) (who : Principal) (r : Loc) (dq : DFrac) (p : PutReq),
  SrvCallTriple (App (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!! go!"Put")) (Val #ctx)) (Val #r))
    iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isServer s γ ∗
        Context.ctxOk ctx ∗ reqPrin ctx who ∗ threadTok ∗ putReqOwn r dq p)
    iprop(threadTok ∗ putReqOwn r dq p) γ who (.put p) false (ClientV3.putReply)

end spec
end EtcdServer
end EtcdGrove
end Perennial
