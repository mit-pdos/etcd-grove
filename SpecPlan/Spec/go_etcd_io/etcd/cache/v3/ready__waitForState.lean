/-
`ready.waitForState` (`cache/*.go`), an internal helper.
Users: `ready.WaitReady`, `ready.WaitNotReady`.
Proof sketch: a loop: the predicate under the mutex (`readyPredFor`); if it holds, `ctx.Err()`; else a `select` on the state channel and `ctx.Done()` (`Context.Done.spec`, `doneRecv.spec`).
Changes: restated over the opaque vocabulary of `Internal.lean` (the old internal handles, ghost names and certificate parameters replaced by predicates over W0's model); the spec mirrors the code.
Margin: none known.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.cache.v3.Internal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Cache

open Iris Iris.BI EtcdModel EtcdWire ClientV3
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- `r.waitForState(ctx, pred)`: `nil` once it saw `pred` hold (for `b = true`, the flag set), or the context's error once done. -/
def ready.waitForState.spec : Prop :=
  ∀ (r : Loc) (ctx : GoInterface) (pred : GoFunc) (b : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗ isReady r ∗ Context.ctxOk ctx ∗ readyPredFor r pred b }}
    (App (App (Val (r @!! go.GoType.PointerType go_etcd_io.etcd.cache.v3.ready.ty @!! go!"waitForState")) (Val #ctx)) (Val #pred))
  {{ (err : GoInterface), RET #err;
      (⌜err = GoInterface.nil⌝ ∗ (if b then readyWasSet r else True)) ∨
      (Context.ctxDone ctx ∗ context.isCtxErr err) }}

end spec

end Cache
end EtcdGrove
end Perennial
