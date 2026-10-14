/-
`recipes.NewPriorityQueue(client, key)` (`client/v3/experimental/recipes/priority_queue.go`). Lean-first (no Rocq counterpart); see
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

/-- **`NewPriorityQueue(client, key)`**, for a client with the recipes' contracts at the empty
prefix (the queue's items are under `key ++ "/"`, `newSequentialKV`'s bookkeeping keys under
`"__" ++ key ++ "/"`): a fresh `*PriorityQueue` holding the client, `context.TODO()` and
`key ++ "/"` (`isPriorityQueue`). -/
abbrev NewPriorityQueue.spec : Prop :=
  ∀ (client : Loc) (key : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.experimental.recipes ∗
      isEtcdRecipesClient client [] }}
    (App (App (Val (@! go_etcd_io.etcd.client.v3.experimental.recipes.NewPriorityQueue))
      (Val #client)) (Val #key))
  {{ (q : Loc), RET #q; isPriorityQueue q client key }}

end spec

end recipes
end EtcdGrove
end Perennial
