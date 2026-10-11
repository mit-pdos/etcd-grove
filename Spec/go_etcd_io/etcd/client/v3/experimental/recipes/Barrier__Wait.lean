/-
`recipes.(*Barrier).Wait()` (`client/v3/experimental/recipes/barrier.go`). Lean-first (no Rocq counterpart); see
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

/-- **`b.Wait()`**, knowing etcd has reached `lo ≥ 0`, for a client whose watch channels never
close (the bundle's premise, `isEtcdRecipesClient`): gets the key at a revision `r0 ≥ lo`; if it
is absent, returns `nil` at once; otherwise waits for a delete of the key from `r0 + 1`
(`WaitEvents`). `nil` means **released**: the key was absent at some revision `r ≥ lo` etcd has
reached (at the get's revision, or at the delete event's). Or the get's error. -/
abbrev Barrier.Wait.spec : Prop :=
  ∀ (b client : Loc) (key : GoString) (lo : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.experimental.recipes ∗
      context.isClosedchanInit ∗ isBarrier b client key ∗ etcdReached lo ∗ ⌜0 ≤ sint.Z lo⌝ }}
    (App (Val (b @!! go.GoType.PointerType Barrier.ty @!! go!"Wait")) (Val #()))
  {{ (err : GoInterface), RET #err;
      (⌜err = GoInterface.nil⌝ ∗ ∃ r : w64, etcdReached r ∗ etcdAbsent key key r ∗
        ⌜sint.Z lo ≤ sint.Z r⌝) ∨
      ⌜err ≠ GoInterface.nil⌝ }}

end spec

end recipes
end EtcdGrove
end Perennial
