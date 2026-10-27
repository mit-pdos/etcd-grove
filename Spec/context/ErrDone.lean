/-
A done context's `Err()`: Go's contract of `context.Context.Err` (the trust boundary).
Lean-first (no Rocq counterpart). Stated over Perennial's context model alone (2026-10-16, stage
R7c: raft's `node.stepWithWaitOption` takes it as a callee too, so it imports nothing of the
server).
-/
module

public import Perennial.Proof.context

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : context.Assumptions]

/-- `ctx.Err()` on a done context (`context.isContext`, its `Done` channel closed,
`ContextClosed`): the value of `context.Canceled` or of `context.DeadlineExceeded`, a typed error.
Go's documented contract of every `Context` (`Err`: "If Done is closed, Err returns a non-nil
error explaining why: DeadlineExceeded if the context's deadline passed, or Canceled if the
context was canceled for some other reason"), kept by the standard contexts (a `cancelCtx`
stores `Canceled`, `DeadlineExceeded` or its parent's `Err()`); Perennial's `isContext` says
only that it is a typed error (`isTypedErr`). The server's `processInternalRaftRequestOnce`
passes `cctx.Err()` to `parseProposeCtxErr`, whose `default` branch (returning the error itself,
which the gRPC layer could not map) this rules out.

Not the same assumption as `context.Err` (`Spec/context/Err.lean`, the cache's), and neither
follows from the other (2026-10-13, the merge of `origin/lean`): that one is for any context and
says only that the error's `Error()` returns; this one is for a done context and says which
error it is, nothing of its `Error()`. -/
abbrev context.ErrDone.spec : Prop :=
  ∀ (c : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗ context.isContext c cd ∗
      context.ContextClosed cd.Done_gn }}
    (App (Val #(methods c.ty go!"Err" c.v)) (Val #()))
  {{ (err : GoInterface), RET #err; ⌜context.isTypedErr err⌝ ∗
      (globalAddr context.Canceled ↦□ err ∨ globalAddr context.DeadlineExceeded ↦□ err) }}

end spec

end EtcdGrove
end Perennial
