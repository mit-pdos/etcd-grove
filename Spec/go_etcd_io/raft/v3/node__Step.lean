/-
## `node.Step(ctx, m)`

**Users.** etcd's `EtcdServer.Process` (`server/etcdserver/server.go:721`), which rafthttp's
`streamReader`/`pipelineHandler`/`snapshotHandler` call with every message received for the local
member (after `IsIDRemoved` checks); the examples' networks (`kvdurable/cluster.go:387`). Snippet:
`transport.go` (`ReqDeliver`).

**Proof sketch.** Not nil; a local type from the network would be ignored (`msgSent` rules it out:
no node sends one); `n.step(ctx, m)` hands it to the run goroutine (`stepOk` from `msgSent`, the
credit and the address), which filters responses from unknown peers and steps it (`raft.Step`, R2:
the credit's proposal updates join the leader's log or are forwarded again). `Step` keeps the message
(`nonissues/raft-step-writes-caller-message.md`): the client gives it up whole.

**Changes.** Over values: the message is `Msg` with `msgSent`/`msgCredit` (was `stepIn`'s bundle of
`sentMsg`, the message's pointer and credits and `snapLocalMsg`); `snapLocalMsg` dropped (a
per-node snapshot directory the examples no longer use).

**Margin.** The error says only how the hand-off ended.
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

/-- **Steps a received message** `m` addressed to node `id`, sent by a node of `γ`, with its credit. -/
def node.Step.spec : Prop :=

  ∀ (n : Loc) (γ : Cluster) (id : w64) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (ml : Loc) (m : Msg),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNode n γ id ∗ context.isContext ctx cd ∗ msgPts ml (DFrac.own 1) m ∗
      msgSent γ m ∗ msgCredit γ m ∗ ⌜m.to = id⌝ }}
    (App (App (Val (n @!! go.GoType.PointerType go_etcd_io.raft.v3.node.ty @!! go!"Step")) (Val #(interface.ok ctx))) (Val #ml))
  {{ (err : GoInterface), RET #err; nodeErr n err }}

end spec
end Raft
end EtcdGrove
end Perennial
