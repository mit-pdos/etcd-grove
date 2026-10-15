/-
`recipes.NewQueue(client, keyPrefix)` (`client/v3/experimental/recipes/queue.go`). Lean-first (no Rocq counterpart); see
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

/-- **`NewQueue(client, keyPrefix)`**, for a non-empty prefix `kp` and a client with the recipes'
contracts at `kp`: a fresh `*Queue` holding the client, `context.TODO()` and `kp` (`isQueue`). -/
abbrev NewQueue.spec : Prop :=
  ∀ (client : Loc) (kp : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.experimental.recipes ∗
      isEtcdRecipesClient client kp ∗ ⌜kp ≠ []⌝ }}
    (App (App (Val (@! go_etcd_io.etcd.client.v3.experimental.recipes.NewQueue)) (Val #client))
      (Val #kp))
  {{ (q : Loc), RET #q; isQueue q client kp }}

end spec

end recipes
end EtcdGrove
end Perennial
