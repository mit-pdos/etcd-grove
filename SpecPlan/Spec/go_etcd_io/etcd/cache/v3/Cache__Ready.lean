/-
`(*Cache).Ready()` (`cache/cache.go`): whether the cache is ready (loaded and watching).

Users: none in etcd's sources besides the package's tests; kept (verified before). Snippet:
`cache/lifecycle.go` `ReqReadyThenGet`.

Proof sketch: `ready.Ready.spec`; `true` means `ready.Set` ran, which the watch loop calls only after
a `Restore` at a revision `≥ 1` (a linearizable read's header revision), so the store's latest
revision is `≥ 1` for good (`storeRevLb`, the cache's invariant ties `readyWasSet` to it).

Changes: from `specs-ref`'s `Cache__Ready.lean` (the ready's epoch): the client-facing fact
`cacheRevLb c 1` instead of the ready's internal epochs.

Margin: readiness can be lost again (an upstream watch failure, `Reset`): `true` says it was ready.
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

/-- **`c.Ready()`**: `true` only once the cache has loaded (its latest revision at least `1`). -/
def Cache.Ready.spec : Prop :=
  ∀ (c : Loc) (γ : Cluster) (who : Principal) (pfx : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗ isCache c γ who pfx }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.cache.v3.Cache.ty @!! go!"Ready")) (Val #()))
  {{ (b : Bool), RET #b; if b then cacheRevLb c 1 else True }}

end spec

end Cache
end EtcdGrove
end Perennial
