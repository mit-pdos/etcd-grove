/-
`recipe.NewQueue(client, keyPrefix)` (`queue.go`).

**Users**: `T/v3_queue_test.go:50,59,153`, `T/v3_closed_watch_test.go:73,136`. Snippet:
`recipes/queue.go`.

**Proof sketch**: `context.TODO()`; allocate; `queueAt`'s realization.

**Changes**: old spec required `kp ≠ []`, a length bound and the recipes' client invariant over the
prefix; now any prefix and any client (the queue's items are whatever keys the prefix holds).

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

/-- **`NewQueue(c, kp)`**: a queue under the prefix `kp`. -/
def NewQueue.spec : Prop :=
  ∀ (c : Loc) (γ : Cluster) (who : Principal) (kp : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.experimental.recipes ∗ isClient c γ who }}
    (App (App (Val (@! go_etcd_io.etcd.client.v3.experimental.recipes.NewQueue)) (Val #c)) (Val #kp))
  {{ (q : Loc), RET #q; queueAt q c γ who kp }}

end spec

end Recipes
end EtcdGrove
end Perennial
