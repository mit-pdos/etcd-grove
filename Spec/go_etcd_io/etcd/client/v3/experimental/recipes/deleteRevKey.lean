/-
`recipes.deleteRevKey(kv, key, rev)` (`client/v3/experimental/recipes/client.go`). Lean-first (no Rocq counterpart);
see `InvRecipesClient.lean`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.experimental.recipes.InvRecipesClient

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

/-- **`deleteRevKey(kv, key, rev)`**, the claim of `key` at mod revision `rev > 0` (under the
prefix `pfx` of `kv`'s contracts), knowing etcd has reached `lo`: the transaction
`If(ModRevision(key) = rev).Then(OpDelete(key))` (`deleteRevTxn`):
* `(true, nil)`: at a revision `r ≥ lo` etcd has reached, the claim succeeded
  (`revKeyDeleted`: `key` had mod revision `rev` at `r - 1` and is absent at `r`), and the
  revision `r` is this call's (`etcdRevToken r`: the delete wrote, so `r` is its own);
* `(false, nil)`: at a revision `r ≥ lo`, `key` does not have mod revision `rev`
  (`revKeyGone`: absent, or modified since);
* `(false, err)` with an error. -/
abbrev deleteRevKey.spec : Prop :=
  ∀ (kv : GoInterfaceOk) (pfx key : GoString) (rev lo : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.experimental.recipes ∗ isRecipesKV (GoInterface.ok kv) pfx ∗ etcdReached lo ∗
      ⌜pfx <+: key ∧ 0 < sint.Z rev⌝ }}
    (App (App (App (Val (@! go_etcd_io.etcd.client.v3.experimental.recipes.deleteRevKey))
      (Val #(GoInterface.ok kv))) (Val #key)) (Val #rev))
  {{ (ok : Bool) (err : GoInterface), RET (PairV #ok #err);
      (⌜err = GoInterface.nil⌝ ∗ ∃ r : w64, etcdReached r ∗
        ⌜sint.Z lo ≤ sint.Z r ∧ sint.Z r < 2 ^ 63 - 1⌝ ∗
        (if ok then revKeyDeleted pfx key rev r ∗ etcdRevToken r else revKeyGone pfx key rev r)) ∨
      ⌜err ≠ GoInterface.nil ∧ ok = false⌝ }}

end spec

end recipes
end EtcdGrove
end Perennial
