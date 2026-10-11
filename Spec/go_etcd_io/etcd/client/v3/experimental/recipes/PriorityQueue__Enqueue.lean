/-
`recipes.(*PriorityQueue).Enqueue(val, pr)` (`client/v3/experimental/recipes/priority_queue.go`). Lean-first (no Rocq counterpart); see
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
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.experimental.recipes.Assumptions]

/-- **`q.Enqueue(val, pr)`**, knowing etcd has reached `lo`: `newSequentialKV(client.KV,
fmt.Sprintf("%s%05d", key ++ "/", pr), val)`: `nil` means a fresh key under
`key ++ "/" ++ <pr, 5 digits> ++ "/"` (the priority, zero-padded: `Sprintf`'s model) was created
with the value `val` at some `r ≥ lo` etcd has reached (`keyCreatedAt`: absent at `r - 1`); or an
error. (That the keys of one priority sort in their order of creation is `newSequentialKV`'s, unit
1b's, under its premise on the keys under the prefix.) -/
abbrev PriorityQueue.Enqueue.spec : Prop :=
  ∀ (q client : Loc) (key val : GoString) (pr : w16) (lo : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.experimental.recipes ∗
      isPriorityQueue q client key ∗ etcdReached lo }}
    (App (App (Val (q @!! go.GoType.PointerType PriorityQueue.ty @!! go!"Enqueue")) (Val #val))
      (Val #pr))
  {{ (err : GoInterface), RET #err;
      (⌜err = GoInterface.nil⌝ ∗ ∃ (k : GoString) (r : w64), etcdReached r ∗
        keyCreatedAt [] k val (W64 0) r ∗
        ⌜(key ++ go!"/" ++ _root_.Perennial.fmt.padZeros 5
            (_root_.Perennial.fmt.decimal (uint.Z pr)) ++ go!"/") <+: k ∧
          sint.Z lo ≤ sint.Z r⌝) ∨
      ⌜err ≠ GoInterface.nil⌝ }}

end spec

end recipes
end EtcdGrove
end Perennial
