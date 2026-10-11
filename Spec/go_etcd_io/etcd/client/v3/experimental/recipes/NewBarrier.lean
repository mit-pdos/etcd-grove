/-
`recipes.NewBarrier(client, key)` (`client/v3/experimental/recipes/barrier.go`). Lean-first (no Rocq counterpart); see
`InvRecipesBarrier.lean`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.experimental.recipes.InvRecipesBarrier

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
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.experimental.recipes.Assumptions]

/-- **`NewBarrier(client, key)`**, for a client with the recipes' contracts at the prefix `key`:
a fresh `*Barrier` holding the client, `context.TODO()` and the key (`isBarrier`). -/
abbrev NewBarrier.spec : Prop :=
  ∀ (client : Loc) (key : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.experimental.recipes ∗
      isEtcdRecipesClient client key }}
    (App (App (Val (@! go_etcd_io.etcd.client.v3.experimental.recipes.NewBarrier)) (Val #client))
      (Val #key))
  {{ (b : Loc), RET #b; isBarrier b client key }}

end spec

end recipes
end EtcdGrove
end Perennial
