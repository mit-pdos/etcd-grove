/-
## `node.ReadIndex(ctx, rctx)`

**Users.** etcd's read loop (`server/etcdserver/read/read.go:236`: a fresh 8-byte id per request,
retried with a new one; `ErrStopped` ends the loop); the examples' `Replica.read`
(`kvdurable/kv.go:811`: cluster-wide unique contexts). Snippet: `readindex.go` (`ReqLinearizableRead`).

**Proof sketch.** `n.step(ctx, MsgReadIndex{rctx})` (`stepOk` of a local read with its registered
context); the run goroutine's `raft.Step` (R2: the leader confirms with a quorum's heartbeat
responses, `ReadOnlySafe` by `ConfigOk`, and fires the read's update at its commit index, recording
`readState γ c i`; a follower forwards it). The read state reaches the client in a `Ready`.

**Changes.** Unchanged (over opaque predicates).

**Margin.** A request may be lost (no read state ever); `nil` says only it was handed over.
-/
module

public import SpecPlan.Spec.go_etcd_io.raft.v3.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Raft

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]
variable [ctx_sem : context.Assumptions]

/-- **Requests a read index** for registered context `c`. -/
def node.ReadIndex.spec : Prop :=

  ∀ (n : Loc) (γ : Cluster) (id : w64) (ctx : GoInterface)
    (rctx : GoSlice) (c : List w8) (Q : List LogEntry → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNode n γ id ∗ Context.ctxOk ctx ∗ ownSlice rctx c DFrac.discard ∗
      readCtx γ c Q }}
    (App (App (Val (n @!! go.GoType.PointerType go_etcd_io.raft.v3.node.ty @!! go!"ReadIndex")) (Val #ctx)) (Val #rctx))
  {{ (err : GoInterface), RET #err; nodeErr n ctx err }}

end spec
end Raft
end EtcdGrove
end Perennial
