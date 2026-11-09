/-
## `node.Propose(ctx, data)`

**Users.** etcd's `EtcdServer.processInternalRaftRequestOnce` (`server/etcdserver/v3_server.go:1114`:
a request id in the data, waited on by `w.Register`; one-shot credit: rafthttp delivers a message at
most once); the examples' `Replica.propose` (`kvdurable/kv.go:776`: retried on error, the operation
id deduplicating at apply; persistent credit when their network duplicates). Snippet: `propose.go`
(`ReqProposeOnce`, `ReqProposeRetry`).

**Proof sketch.** `stepWait(ctx, MsgProp{data})`: the client's update rides with the message
(`stepOk` of a local proposal) into the run goroutine; `raft.Step` (R2) either appends it at the
leader (the update deposited with the entry, fired when it commits: `committedOps` grows by
`opsOf [entry]`), forwards it in a `MsgProp` (the update in that message's `msgCredit`), or drops it
(`ErrProposalDropped`; the update is dropped unfired, or, with `γ.dup`, kept by the copies). The
result comes back on the proposal's channel; `ctx` or `done` may end the wait first.

**Changes.** The update's commit is `ops ++ opsOf [entry]` (an empty proposal is a filler, which the
operations leave out); otherwise unchanged.

**Margin.** An error does not mean the proposal was dropped (it may still commit); `nil` does not mean
it will commit (`Node.Propose`'s documentation: proposals can be lost).
-/
module

public import Spec.go_etcd_io.raft.v3.Api

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

/-- **Proposes `data`**: the client's update (persistent if `γ.dup`) fires at most once per copy, when
the entry commits (at some term `t`). Errors: the node's, or `ErrProposalDropped`. -/
def node.Propose.spec : Prop :=

  ∀ (n : Loc) (γ : Cluster) (id : w64) (ctx : GoInterface)
    (data_sl : GoSlice) (data : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNode n γ id ∗ Context.ctxOk ctx ∗ ownSlice data_sl data DFrac.discard ∗
      (□?γ.dup AU <{ ∃∃ (ops : List LogEntry), committedOps γ ops }> @ ⊤ \ ↑γ.ns, ∅
        <{ ∀∀ (t : w64), committedOps γ (ops ++ opsOf [⟨t, EntryNormal, data⟩]), COMM True }>) }}
    (App (App (Val (n @!! go.GoType.PointerType go_etcd_io.raft.v3.node.ty @!! go!"Propose")) (Val #ctx)) (Val #data_sl))
  {{ (err : GoInterface), RET #err; propErr n ctx err }}

end spec
end Raft
end EtcdGrove
end Perennial
