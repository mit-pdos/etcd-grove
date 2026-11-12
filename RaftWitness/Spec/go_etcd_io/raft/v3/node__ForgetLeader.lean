/- Lean-first (no Rocq counterpart).

## `node.ForgetLeader(ctx)` (node.go:604), 2026-10-13

From any goroutine: `step` of `pb.Message{Type: MsgForgetLeader}` (`netP_local`), which
`run` steps as `RawNode.ForgetLeader` does: a follower forgets its leader. Until stage R7a
specified for `context.Background()`; the error said only whether the message reached `run`.
(2026-10-16, stage R7a, D10 gap (2)) The context is any `nodeCtx ctx cd` (`InvNodeCtx.lean`:
`Done()` nil, or Perennial's `isContext`), and the error `nodeErr cd err`: `nil`, raft's
`ErrStopped`, or the context's once its `Done()` fired (`ctxErr`).
-/
module

public import RaftWitness.Proof.go_etcd_io.raft.v3.InvNodeCtx
public import Perennial.Proof.context

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

/-- See the file header. -/
abbrev node.ForgetLeader.spec : Prop :=
  ∀ (γ : NodeNames) (id : w64) (n : Loc)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNode γ id n ∗ nodeCtx ctx cd }}
    (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"ForgetLeader"))
      (Val #(interface.ok ctx)))
  {{ (err : GoInterface), RET #err; nodeErr cd err }}

end spec

end EtcdGrove
end Perennial
