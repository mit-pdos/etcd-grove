/-
`conditionalProgressRequestor.run` (`cache/*.go`), an internal helper.
Users: `newCache`'s goroutine.
Proof sketch: forks the stopper (on `ctx.Done()`, `stopped = true` and `Signal`); a timer from the clock (`clockOk`); a loop waiting on the `Cond` while nobody waits, then on the timer or the context, calling the notifier's `RequestProgress` (`progressNotifierOk`); returns once stopped or the context done.
Changes: restated over the opaque vocabulary of `Internal.lean` (the old internal handles, ghost names and certificate parameters replaced by predicates over W0's model); the spec mirrors the code.
Margin: none known.
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.Internal

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

/-- `p.run(ctx)`: returns (once the context is done). -/
def conditionalProgressRequestor.run.spec : Prop :=
  ∀ (p : Loc) (ctx : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗ isProgressRequestor p ∗ Context.ctxOk ctx }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.cache.v3.conditionalProgressRequestor.ty @!! go!"run")) (Val #ctx))
  {{ RET #(); True }}

end spec

end Cache
end EtcdGrove
end Perennial
