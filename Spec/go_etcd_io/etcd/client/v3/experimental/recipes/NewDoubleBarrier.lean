/-
`recipe.NewDoubleBarrier(s, key, count)` (`double_barrier.go`).

**Users**: `T/v3_double_barrier_test.go:43,55,114,134,184,193`, `T/v3_closed_watch_test.go:215`.
Snippet: `recipes/doublebarrier.go`.

**Proof sketch**: `context.TODO()`; allocate; `dbOwn`'s realization.

**Changes**: old `isDoubleBarrier` took `concurrency.isSession` and the recipes' client invariant;
now `sessionAt` (1d's slot). Any `count` (`count ≤ 0`: every `Enter` is `ErrTooManyClients`).

**Margin**: none.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.experimental.recipes.Api

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

/-- **`NewDoubleBarrier(s, key, count)`**: a double barrier on `key` for `count` processes, holding no key. -/
def NewDoubleBarrier.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster) (who : Principal) (id : w64) (key : GoString) (count : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.experimental.recipes ∗ sessionAt s γ who id }}
    (App (App (App (Val (@! go_etcd_io.etcd.client.v3.experimental.recipes.NewDoubleBarrier)) (Val #s))
      (Val #key)) (Val #count))
  {{ (b : Loc), RET #b; dbOwn b γ who key count id none }}

end spec

end Recipes
end EtcdGrove
end Perennial
