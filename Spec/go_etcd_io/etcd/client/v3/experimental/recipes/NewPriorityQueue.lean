/-
`recipe.NewPriorityQueue(client, key)` (`priority_queue.go`): its keys are under `key + "/"`.

**Users**: `T/v3_queue_test.go:100,161`, `T/v3_closed_watch_test.go:76`. Snippet: `recipes/pqueue.go`.

**Proof sketch**: `context.TODO()`; the string concatenation; allocate; `pqueueAt`'s realization.

**Changes**: as `NewQueue`'s.

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

/-- **`NewPriorityQueue(c, key)`**: a priority queue on `key`. -/
def NewPriorityQueue.spec : Prop :=
  ∀ (c : Loc) (γ : Cluster) (who : Principal) (key : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.experimental.recipes ∗ isClient c γ who }}
    (App (App (Val (@! go_etcd_io.etcd.client.v3.experimental.recipes.NewPriorityQueue)) (Val #c))
      (Val #key))
  {{ (q : Loc), RET #q; pqueueAt q c γ who key }}

end spec

end Recipes
end EtcdGrove
end Perennial
