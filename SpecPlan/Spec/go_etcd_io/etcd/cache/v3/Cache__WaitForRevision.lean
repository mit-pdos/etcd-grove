/-
`(*Cache).WaitForRevision(ctx, rev)` (`cache/cache.go`): poll until the cache reached `rev`.

Users: etcd's integration tests (`testGet`: `WaitForRevision(ctx, baseRev)` after writes, then
`Get`s; `testWithPrefixGet`: after `RequestProgress`). Snippet: `cache/get.go`
`ReqWaitThenSerializable`.

Proof sketch: a loop: `store.LatestRev.spec` (`storeRevLb s r` of what it read); `r ≥ rev` returns
`nil` with `cacheRevLb c rev`; else a `select` on `time.After(10ms)` (Perennial's `time` specs) and
`ctx.Done()` (W0's context bundle, the `Done` triple asked of W0: `req/context.md`), whose context
branch returns `ctx.Err()`, non-`nil` (`Context.ErrDone.spec`).

Changes: (round 1) a thread token, given back, for the read lock's reader slot. from `specs-ref`'s `Cache__WaitForRevision.lean`: W0's context bundle; the client-facing
`cacheRevLb`.

Margin: none.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.cache.v3.Api

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

/-- **`c.WaitForRevision(ctx, rev)`**: `nil` once the cache's latest revision is at least `rev`, or
the context's error once it is done. -/
def Cache.WaitForRevision.spec : Prop :=
  ∀ (c : Loc) (γ : Cluster) (who : Principal) (pfx : GoString) (ctx : GoInterface) (rev : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗ isCache c γ who pfx ∗ Context.ctxOk ctx ∗ threadTok }}
    (App (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.cache.v3.Cache.ty @!! go!"WaitForRevision")) (Val #ctx)) (Val #rev))
  {{ (err : GoInterface), RET #err; threadTok ∗
      (⌜err = GoInterface.nil⌝ ∗ cacheRevLb c (sint.Z rev).toNat) ∨
      (Context.ctxDone ctx ∗ context.isCtxErr err) }}

end spec

end Cache
end EtcdGrove
end Perennial
