/-
`recipe.NewBarrier(client, key)` (`barrier.go`).

**Users**: `T/v3_barrier_test.go:43,58,104`, `T/v3_closed_watch_test.go:176,181`. Snippet:
`recipes/barrier.go`.

**Proof sketch**: `context.TODO()` (`ctxOk`); allocate; `barrierAt`'s realization (the fields,
persistent).

**Changes**: old `isBarrier` took the recipes' client invariant; now `isClient` (any client of `γ`).

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

/-- **`NewBarrier(c, key)`**: a barrier on `key` over the client. -/
def NewBarrier.spec : Prop :=
  ∀ (c : Loc) (γ : Cluster) (who : Principal) (key : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.experimental.recipes ∗ isClient c γ who }}
    (App (App (Val (@! go_etcd_io.etcd.client.v3.experimental.recipes.NewBarrier)) (Val #c)) (Val #key))
  {{ (b : Loc), RET #b; barrierAt b c γ who key }}

end spec

end Recipes
end EtcdGrove
end Perennial
