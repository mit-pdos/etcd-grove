/- Lean-first (no Rocq counterpart).

## `node.ForgetLeader(ctx)` (node.go:604)

The node API's spec. (2026-10-29, stage U9a: over `isNode`; until then over raft's internals,
`isNodeChan` and `NodeNames`, now the proof's private `node.ForgetLeader.specRaw`.)
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

/-- **`node.ForgetLeader(ctx)`**, from any goroutine: a local `MsgForgetLeader` stepped by the
node (a follower forgets its leader); nothing is promised of its effect. The error says only whether
the message reached the node (`nodeErr`: `nil`, `ErrStopped`, or the context's). (raft-final, 2026-10-29, K5: the stopped answer carries `nodeStopped`, `nodeErrS`; until then
`nodeErr`, which `nodeErrS_nodeErr` gives back.) -/
abbrev node.ForgetLeader.spec : Prop :=
  ∀ (n : Loc) (γ : Cluster) (N : Namespace) (id : w64)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNode n γ N id ∗ nodeCtx ctx cd }}
    (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"ForgetLeader"))
      (Val #(interface.ok ctx)))
  {{ (err : GoInterface), RET #err; nodeErrS n γ N cd err }}

end spec

end EtcdGrove
end Perennial
