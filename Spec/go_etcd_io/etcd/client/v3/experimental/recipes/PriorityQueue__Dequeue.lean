/-
`recipes.(*PriorityQueue).Dequeue()` (`client/v3/experimental/recipes/priority_queue.go`). Lean-first (no Rocq counterpart); see
`InvRecipesQueue.lean`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.experimental.recipes.InvRecipesQueue

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace recipes

open Iris Iris.BI go_etcd_io.etcd.client.v3.experimental.recipes go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.experimental.recipes.Assumptions]

/-- **`q.Dequeue()`**, knowing etcd has reached `lo ≥ 0`, for a client whose watch channels never
close (the bundle's premise, `isEtcdRecipesClient`): as `Queue.Dequeue`, on the items under
`key ++ "/"`, with the get `WithFirstKey()` (the least key):
* `(v, nil)`: an item `it` under `key ++ "/"` with the value `v` was **dequeued by this call** at
  some `r ≥ lo` etcd has reached (`dequeuedAt`, with the token of the revision `r`), **in order**
  (`dequeueOrder` for `keyLe`: at the last get's revision `r0 < r`, it was there with the least
  key under `key ++ "/"`; or the items under `key ++ "/"` then were all claimed by others by `r`,
  and it was put at or after `r0`);
* `("", err)` with an error (the get's, a claim's). -/
abbrev PriorityQueue.Dequeue.spec : Prop :=
  ∀ (q client : Loc) (key : GoString) (lo : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.experimental.recipes ∗
      context.isClosedchanInit ∗ isPriorityQueue q client key ∗ etcdReached lo ∗
      ⌜0 ≤ sint.Z lo⌝ }}
    (App (Val (q @!! go.GoType.PointerType PriorityQueue.ty @!! go!"Dequeue")) (Val #()))
  {{ (v : GoString) (err : GoInterface), RET (PairV #v #err);
      (⌜err = GoInterface.nil⌝ ∗ ∃ (it : EtcdKv) (r : w64), etcdReached r ∗
        dequeuedAt [] (key ++ go!"/") it r ∗ dequeueOrder [] (key ++ go!"/") keyLe it r ∗
        ⌜v = it.value ∧ sint.Z lo ≤ sint.Z r⌝) ∨
      ⌜err ≠ GoInterface.nil⌝ }}

end spec

end recipes
end EtcdGrove
end Perennial
