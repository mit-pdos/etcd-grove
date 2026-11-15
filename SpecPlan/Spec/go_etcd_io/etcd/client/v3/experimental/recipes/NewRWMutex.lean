/-
`recipe.NewRWMutex(s, prefix)` (`rwmutex.go`): its keys under `prefix + "/"`, `myKey` `nil`.

**Users**: `T/v3_lock_test.go:324`. Snippet: `recipes/rwmutex.go`.

**Proof sketch**: `context.TODO()`; allocate; `rwmOwn`'s realization (the session's `isSession`, its client's `isClient`).

**Changes**: old `isRWMutex` took `concurrency.isSession` and the recipes' client invariant; now
1d's `isSession s c γ id` with `isClient c γ who` (integration: was a slot).

**Margin**: none.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.client.v3.experimental.recipes.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Recipes

open Iris Iris.BI EtcdModel EtcdWire ClientV3
open go_etcd_io.etcd.client.v3.experimental.recipes

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.experimental.recipes.Assumptions]

/-- **`NewRWMutex(s, prefix)`**: a readers-writer mutex on `prefix/`, holding no key. -/
def NewRWMutex.spec : Prop :=
  ∀ (s c : Loc) (γ : Cluster) (who : Principal) (id : w64) (pre : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.experimental.recipes ∗ Concurrency.isSession s c γ id ∗ isClient c γ who }}
    (App (App (Val (@! go_etcd_io.etcd.client.v3.experimental.recipes.NewRWMutex)) (Val #s)) (Val #pre))
  {{ (m : Loc), RET #m; rwmOwn m γ who id (pre ++ go!"/") none }}

end spec

end Recipes
end EtcdGrove
end Perennial
