/-
`recipes.NewDoubleBarrier(s, key, count)` (`client/v3/experimental/recipes/double_barrier.go`). Lean-first (no Rocq
counterpart); see `InvDoubleBarrier.lean`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.experimental.recipes.InvDoubleBarrier

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

/-- **`NewDoubleBarrier(s, key, count)`**, for a session `s` (of `client`, with the lease `id`)
whose client has the recipes' contracts at `key ++ "/"`, and **`count > 0`** (with `count ≤ 0`,
`Enter` always fails, and its `Kvs[count-1]` would be out of range): the barrier (its context
`context.TODO()`), with no key (`myKey` nil). -/
abbrev NewDoubleBarrier.spec : Prop :=
  ∀ (s : Loc) (γ : concurrency.SessionNames) (client : Loc) (id : w64) (key : GoString)
    (count : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.experimental.recipes ∗ concurrency.isSession s γ client id ∗
      isEtcdRecipesClient client (key ++ go!"/") ∗ context.isClosedchanInit ∗ ⌜0 < sint.Z count⌝ }}
    (App (App (App (Val (@! go_etcd_io.etcd.client.v3.experimental.recipes.NewDoubleBarrier))
      (Val #s)) (Val #key)) (Val #count))
  {{ (b : Loc), RET #b; isDoubleBarrier b s γ client id key count ∗
      dbMyKey b (key ++ go!"/") none }}

end spec

end recipes
end EtcdGrove
end Perennial
