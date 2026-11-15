/-
**A `*cancelCtx` child of `Background()`** (k8s 7f-4, Addendum T-i, 2026-11-13): the context
`context.WithCancel(context.Background())` returns, as a persistent fact of its type and parent field;
what net/http's round trippers need of a request's context (`http.reqCtxBg`,
`notes/roundtripper-ctx-refuted.md`). Lean-first.
-/
module

public import Perennial.Proof.context

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`ctx` is a `*cancelCtx` whose parent is `Background()`** (persistent; k8s 7f-4, Addendum T-i):
what `context.WithCancel(context.Background())` returns (`context.WithCancelBackground.spec`).
In Go such a context answers `Value` at every key but `&cancelCtxKey` with `Background()`'s `nil`
(`cancelCtx.Value` asks its parent), has no deadline, and its `Err()` and `context.Cause` are `nil`,
then `context.Canceled` once its `cancel` runs (its parent is never done). The one other Go
function that makes a `*cancelCtx` over `Background()` is `WithCancelCause`, whose cancel stores the
caller's cause; Perennial has no spec of it, so a verified program cannot make one; a spec of it
must not give this fact (`etc/bgcancel-check.py`, run by `etc/gates.sh`, fails if the pinned Perennial
gains one). The `cancelCtx` embedded in a `*timerCtx` also has a `ctxField ↦□` fact in Perennial's
`ctxChain` (its parent may be `Background()`, with `WithDeadlineCause`'s program cause), but as an
interface value of type `*cancelCtx` it exists only as `Value(&cancelCtxKey)`'s answer, and that key is
unexported, so a program outside `context` cannot hold it as a context (k8s 7f-4, T-i review, m2). -/
def context.bgCancelChild (ctx : GoInterfaceOk) : IProp GF :=
  iprop(∃ c : Loc, ⌜ctx = interface.mk (go.GoType.PointerType _root_.Perennial.context.cancelCtx.ty) #c⌝ ∗
    _root_.Perennial.context.ctxField c ↦□
      (interface.ok _root_.Perennial.context.backgroundCtxVal : GoInterface))

instance context.bgCancelChild_persistent (ctx : GoInterfaceOk) :
    Persistent (context.bgCancelChild (GF := GF) ctx) := by
  unfold context.bgCancelChild; infer_instance

end defs

end EtcdGrove
end Perennial
