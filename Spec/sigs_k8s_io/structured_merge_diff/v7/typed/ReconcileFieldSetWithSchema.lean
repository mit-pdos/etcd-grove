/-
`typed.ReconcileFieldSetWithSchema(fieldset, tv)`: the field set reconciled with the schema of the
typed value (`reconcile`: every subtree below a node whose type is now atomic collapsed to that
node), as `nil` when there is nothing to change, or a fresh set. Either way `reconcile S t s` is
what the caller keeps (`Updater.reconcileManagedFieldsWithSchemaChanges` keeps `s` on `nil`). No
error in the scope.

Margin: `r` is `nil` exactly when no atomic node with children was found and the root's type is
not an atomic list (`reconOut S t [] false s = none`); the post says only that `nil` means
`reconcile S t s = s` (`reconcile_id`'s case), which is what the caller needs.

Draft (2026-11-19, notes/smd-plan.md, "The call DAG": the `typed` rows).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.Base
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.Walkers

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI
open sigs_k8s_io.structured_merge_diff.v7

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : typed.Assumptions]

/-- See the file header. -/
abbrev typed.ReconcileFieldSetWithSchema.spec : Prop :=
  ∀ (fp p sc : Loc) (S : Schema) (t : TypeRef) (x : UVal) (s : PathSet),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ isSet fp s ∗ isTV p sc S t x }}
    (App (App (Val (@! _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.ReconcileFieldSetWithSchema)) (Val #fp)) (Val #p))
  {{ (r : Loc) (err : GoInterface), RET (PairV #r #err); ⌜err = interface.nil⌝ ∗
      (⌜r = null ∧ reconcile S t s = s⌝ ∨ isSet r (reconcile S t s)) }}

end spec

end smd
end EtcdGrove
end Perennial
