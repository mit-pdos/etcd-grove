/-
`recipes.(*Queue).Enqueue(val)` (`client/v3/experimental/recipes/queue.go`). Lean-first (no Rocq counterpart); see
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

/-- **`q.Enqueue(val)`**, knowing etcd has reached `lo`: `newUniqueKV(client.KV, kp, val)`: `nil`
means a fresh key under `kp ++ "/"` was created with the value `val` at some `r ≥ lo` etcd has
reached (`keyCreatedAt`: absent at `r - 1`; its mod revision `r` is its place in the queue); or
an error. -/
abbrev Queue.Enqueue.spec : Prop :=
  ∀ (q client : Loc) (kp val : GoString) (lo : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.experimental.recipes ∗
      isQueue q client kp ∗ etcdReached lo }}
    (App (Val (q @!! go.GoType.PointerType Queue.ty @!! go!"Enqueue")) (Val #val))
  {{ (err : GoInterface), RET #err;
      (⌜err = GoInterface.nil⌝ ∗ ∃ (key : GoString) (r : w64), etcdReached r ∗
        keyCreatedAt kp key val (W64 0) r ∗ ⌜(kp ++ go!"/") <+: key ∧ sint.Z lo ≤ sint.Z r⌝) ∨
      ⌜err ≠ GoInterface.nil⌝ }}

end spec

end recipes
end EtcdGrove
end Perennial
