/-
`merge.Updater.addBackOwnedItemsForVersion`:
not proved yet (`sorry`): Draft of the `merge` package's per-function specs (notes/smd-plan.md,
"The call DAG"); proved in the stage's Prove step, after the freeze.
Callees in other packages, whose Draft specs are written beside this one and become hypotheses here
when they are linked: `typed.TypedValue.ToFieldSet`, `typed.TypedValue.Schema`,
`typed.TypedValue.TypeRef`, `fieldpath.Set.EnsureNamedFieldsAreMembers`, `fieldpath.Set.Union`,
`fieldpath.Set.Difference`, `typed.TypedValue.RemoveItems`.

Lean-first (2026-11-19).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.merge.Updater__addBackOwnedItemsForVersion
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__Difference
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__EnsureNamedFieldsAreMembers
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__Union
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.TypedValue__RemoveItems_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.TypedValue__Schema_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.TypedValue__ToFieldSet_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.TypedValue__TypeRef_ptr

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open sigs_k8s_io.structured_merge_diff.v7

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : merge.Assumptions]

theorem merge.Updater.addBackOwnedItemsForVersion.wp_proof
    (h_Set_Difference : fieldpath.Set.Difference.spec (GF := GF))
    (h_Set_EnsureNamedFieldsAreMembers : fieldpath.Set.EnsureNamedFieldsAreMembers.spec (GF := GF))
    (h_Set_Union : fieldpath.Set.Union.spec (GF := GF))
    (h_TypedValue_RemoveItems_ptr : typed.TypedValue.RemoveItems_ptr.spec (GF := GF))
    (h_TypedValue_Schema_ptr : typed.TypedValue.Schema_ptr.spec (GF := GF))
    (h_TypedValue_ToFieldSet_ptr : typed.TypedValue.ToFieldSet_ptr.spec (GF := GF))
    (h_TypedValue_TypeRef_ptr : typed.TypedValue.TypeRef_ptr.spec (GF := GF)) :
    merge.Updater.addBackOwnedItemsForVersion.spec (GF := GF) := by
  sorry

end proof

end smd
end EtcdGrove
end Perennial
