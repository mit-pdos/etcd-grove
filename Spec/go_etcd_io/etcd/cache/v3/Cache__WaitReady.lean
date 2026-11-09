/-
`(*Cache).WaitReady(ctx)` (`cache/cache.go`): wait until the cache is ready or the context is done.

Users: `Cache.Watch`, `Cache.Get` (internally); etcd's integration tests after every `New`
(`if err := c.WaitReady(ctx); err != nil { t.Fatalf }`). Snippet: `cache/lifecycle.go`
`ReqReadyThenGet`.

Proof sketch: `ready.WaitReady.spec`: `nil` once it saw the ready flag set (then `cacheRevLb c 1`, as
for `Ready`), or the context's error once it is done (`waitForState` returns `ctx.Err()` even when
ready: then the context is done, `Context.Err.spec`).

Changes: from `specs-ref`'s `Cache__WaitReady.lean`: W0's context bundle (`Context.ctxOk`) instead of
Perennial's `isContext` (the callers pass any context); the client-facing `cacheRevLb c 1`.

Margin: none.
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Cache

open Iris Iris.BI EtcdModel EtcdWire ClientV3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- **`c.WaitReady(ctx)`**: `nil` once the cache has loaded, or the context's error once it is
done. -/
def Cache.WaitReady.spec : Prop :=
  ∀ (c : Loc) (γ : Cluster) (who : Principal) (pfx : GoString) (ctx : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗ isCache c γ who pfx ∗ Context.ctxOk ctx }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.cache.v3.Cache.ty @!! go!"WaitReady")) (Val #ctx))
  {{ (err : GoInterface), RET #err;
      (⌜err = GoInterface.nil⌝ ∗ cacheRevLb c 1) ∨ (Context.ctxDone ctx ∗ context.isCtxErr err) }}

end spec

end Cache
end EtcdGrove
end Perennial
