/- Lean-first (no Rocq counterpart).

## `node.Campaign(ctx)` (node.go:467)

The node API's spec (2026-10-29, stage U7). The message is raft-internal (`MsgHup` is no network
message): the proof's raw triple, `node.Campaign.specRaw`, is over `isNodeChan`, and the
campaign's term is paid for by a time receipt of `Campaign`'s own Go steps (as `Tick`'s).
-/
module

public import Proof.go_etcd_io.raft.v3.InvNode

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **`node.Campaign(ctx)`**, from any goroutine: a local `MsgHup` stepped by the node (it starts
an election, or a pre-election with `Config.PreVote`, unless it is a leader or cannot be one);
nothing is promised of its effect. The error says only whether
the message reached the node (`nodeErr`: `nil`, `ErrStopped`, or the context's). -/
abbrev node.Campaign.spec : Prop :=
  ∀ (n : Loc) (γ : Cluster) (N : Namespace) (id : w64)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNode n γ N id ∗ nodeCtx ctx cd }}
    (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"Campaign"))
      (Val #(interface.ok ctx)))
  {{ (err : GoInterface), RET #err; nodeErr cd err }}

end spec

end EtcdGrove
end Perennial
