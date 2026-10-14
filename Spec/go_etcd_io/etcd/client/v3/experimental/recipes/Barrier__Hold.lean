/-
`recipes.(*Barrier).Hold()` (`client/v3/experimental/recipes/barrier.go`). Lean-first (no Rocq counterpart); see
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
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.experimental.recipes.Assumptions]

/-- **`b.Hold()`**, knowing etcd has reached `lo`: `newKey(client.KV, key, NoLease)`, the key
created if absent (`putNewKV`'s transaction):
* `nil`: the key was created at some `r ≥ lo` etcd has reached, empty, with no lease
  (`keyCreatedAt`: absent at `r - 1`);
* `ErrKeyExists`: the key was present at some `r ≥ lo` etcd has reached (held already);
* another error. -/
abbrev Barrier.Hold.spec : Prop :=
  ∀ (b client : Loc) (key : GoString) (lo : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.experimental.recipes ∗
      isBarrier b client key ∗ etcdReached lo }}
    (App (Val (b @!! go.GoType.PointerType Barrier.ty @!! go!"Hold")) (Val #()))
  {{ (err : GoInterface), RET #err;
      (⌜err = GoInterface.nil⌝ ∗ ∃ r : w64, etcdReached r ∗ keyCreatedAt key key [] (W64 0) r ∗
        ⌜sint.Z lo ≤ sint.Z r⌝) ∨
      (concurrency.isPkgErr ErrKeyExists err ∗ ∃ r : w64, etcdReached r ∗ etcdPresent key key r ∗
        ⌜sint.Z lo ≤ sint.Z r⌝) ∨
      ⌜err ≠ GoInterface.nil⌝ }}

end spec

end recipes
end EtcdGrove
end Perennial
