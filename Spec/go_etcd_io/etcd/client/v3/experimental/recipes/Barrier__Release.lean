/-
`recipes.(*Barrier).Release()` (`client/v3/experimental/recipes/barrier.go`). Lean-first (no Rocq counterpart); see
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

/-- **`b.Release()`**, knowing etcd has reached `lo`: `client.KV.Delete(ctx, key)`: `nil` means
the key was absent at some `r ≥ lo` etcd has reached (deleted, or already gone); or an error. -/
abbrev Barrier.Release.spec : Prop :=
  ∀ (b client : Loc) (key : GoString) (lo : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.experimental.recipes ∗
      isBarrier b client key ∗ etcdReached lo }}
    (App (Val (b @!! go.GoType.PointerType Barrier.ty @!! go!"Release")) (Val #()))
  {{ (err : GoInterface), RET #err;
      (⌜err = GoInterface.nil⌝ ∗ ∃ r : w64, etcdReached r ∗ etcdAbsent key key r ∗
        ⌜sint.Z lo ≤ sint.Z r⌝) ∨
      ⌜err ≠ GoInterface.nil⌝ }}

end spec

end recipes
end EtcdGrove
end Perennial
