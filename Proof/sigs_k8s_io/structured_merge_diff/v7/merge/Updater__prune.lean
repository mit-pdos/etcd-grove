/-
`merge.Updater.prune`:
not proved yet (`sorry`): Draft of the `merge` package's per-function specs (notes/smd-plan.md,
"The call DAG"); proved in the stage's Prove step, after the freeze.
Callees in other packages, whose Draft specs are written beside this one and become hypotheses here
when they are linked: `fieldpath.versionedSet.Set`, `fieldpath.versionedSet.APIVersion`,
`fieldpath.Set.Empty`, `typed.TypedValue.Schema`, `typed.TypedValue.TypeRef`,
`fieldpath.Set.EnsureNamedFieldsAreMembers`, `typed.TypedValue.RemoveItems`.

Lean-first (2026-11-19).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.merge.Updater__prune
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__Empty
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__EnsureNamedFieldsAreMembers
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.versionedSet__APIVersion
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.versionedSet__Set
public import Spec.sigs_k8s_io.structured_merge_diff.v7.merge.Updater__addBackDanglingItems
public import Spec.sigs_k8s_io.structured_merge_diff.v7.merge.Updater__addBackOwnedItems
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.TypedValue__RemoveItems_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.TypedValue__Schema_ptr
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

theorem merge.Updater.prune.wp_proof
    (h_Set_Empty : fieldpath.Set.Empty.spec (GF := GF))
    (h_Set_EnsureNamedFieldsAreMembers : fieldpath.Set.EnsureNamedFieldsAreMembers.spec (GF := GF))
    (h_versionedSet_APIVersion : fieldpath.versionedSet.APIVersion.spec (GF := GF))
    (h_versionedSet_Set : fieldpath.versionedSet.Set.spec (GF := GF))
    (h_Updater_addBackDanglingItems : merge.Updater.addBackDanglingItems.spec (GF := GF))
    (h_Updater_addBackOwnedItems : merge.Updater.addBackOwnedItems.spec (GF := GF))
    (h_TypedValue_RemoveItems_ptr : typed.TypedValue.RemoveItems_ptr.spec (GF := GF))
    (h_TypedValue_Schema_ptr : typed.TypedValue.Schema_ptr.spec (GF := GF))
    (h_TypedValue_TypeRef_ptr : typed.TypedValue.TypeRef_ptr.spec (GF := GF)) :
    merge.Updater.prune.spec (GF := GF) := by
  sorry

end proof

end smd
end EtcdGrove
end Perennial
