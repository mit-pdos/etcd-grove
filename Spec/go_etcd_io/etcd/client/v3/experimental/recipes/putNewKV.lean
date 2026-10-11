/-
`recipes.putNewKV(kv, key, val, leaseID)` (`client/v3/experimental/recipes/key.go`). Lean-first (no Rocq counterpart);
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
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.experimental.recipes.Assumptions]

/-- **`putNewKV(kv, key, val, leaseID)`**, for a key under the prefix `pfx` of `kv`'s contracts,
knowing etcd has reached `lo`: the transaction `If(Version(key) = 0).Then(OpPut(key, val,
WithLease(leaseID)))` (`newKeyTxn`):
* `(r, nil)`: `key` was created at `r ≥ lo` with `val` and `leaseID` (`keyCreatedAt`: absent at
  `r - 1`, at `r` with create and mod revision `r`), and etcd has reached `r`;
* `(0, ErrKeyExists)`: `key` was present at some `r ≥ lo` etcd has reached;
* any other error (the client's: it may be any value, `ErrKeyExists`'s too, so this case does
  not exclude the previous one). -/
abbrev putNewKV.spec : Prop :=
  ∀ (kv : GoInterfaceOk) (pfx key val : GoString) (lease lo : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.experimental.recipes ∗ isRecipesKV (GoInterface.ok kv) pfx ∗ etcdReached lo ∗ ⌜pfx <+: key⌝ }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.client.v3.experimental.recipes.putNewKV))
      (Val #(GoInterface.ok kv))) (Val #key)) (Val #val)) (Val #lease))
  {{ (rev : w64) (err : GoInterface), RET (PairV #rev #err);
      (⌜err = GoInterface.nil⌝ ∗ etcdReached rev ∗ keyCreatedAt pfx key val lease rev ∗
        ⌜sint.Z lo ≤ sint.Z rev ∧ sint.Z rev < 2 ^ 63 - 1⌝) ∨
      (concurrency.isPkgErr ErrKeyExists err ∗ ⌜rev = W64 0⌝ ∗ ∃ r : w64, etcdReached r ∗
        etcdPresent pfx key r ∗ ⌜sint.Z lo ≤ sint.Z r⌝) ∨
      ⌜err ≠ GoInterface.nil ∧ rev = W64 0⌝ }}

end spec

end recipes
end EtcdGrove
end Perennial
