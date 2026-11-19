/-
`merge.Updater.update`:
not proved yet (`sorry`): Draft of the `merge` package's per-function specs (notes/smd-plan.md,
"The call DAG"); proved in the stage's Prove step, after the freeze.
Callees in other packages, whose Draft specs are written beside this one and become hypotheses here
when they are linked: `typed.TypedValue.Compare`, `typed.Comparison.FilterFields`,
`fieldpath.versionedSet.Set`, `fieldpath.versionedSet.APIVersion`, `fieldpath.versionedSet.Applied`,
`fieldpath.Set.Union`, `fieldpath.Set.Intersection`, `fieldpath.Set.Difference`,
`fieldpath.Set.Empty`.

Lean-first (2026-11-19).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.merge.Updater__update
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.NewVersionedSet
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__Difference
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__Empty
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__Intersection
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__Union
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.versionedSet__APIVersion
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.versionedSet__Applied
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.versionedSet__Set
public import Spec.sigs_k8s_io.structured_merge_diff.v7.merge.ConflictsFromManagers
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.Comparison__ExcludeFields
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.Comparison__FilterFields
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.TypedValue__Compare_ptr

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

theorem merge.Updater.update.wp_proof
    (h_NewVersionedSet : fieldpath.NewVersionedSet.spec (GF := GF))
    (h_Set_Difference : fieldpath.Set.Difference.spec (GF := GF))
    (h_Set_Empty : fieldpath.Set.Empty.spec (GF := GF))
    (h_Set_Intersection : fieldpath.Set.Intersection.spec (GF := GF))
    (h_Set_Union : fieldpath.Set.Union.spec (GF := GF))
    (h_versionedSet_APIVersion : fieldpath.versionedSet.APIVersion.spec (GF := GF))
    (h_versionedSet_Applied : fieldpath.versionedSet.Applied.spec (GF := GF))
    (h_versionedSet_Set : fieldpath.versionedSet.Set.spec (GF := GF))
    (h_ConflictsFromManagers : merge.ConflictsFromManagers.spec (GF := GF))
    (h_Comparison_ExcludeFields : typed.Comparison.ExcludeFields.spec (GF := GF))
    (h_Comparison_FilterFields : typed.Comparison.FilterFields.spec (GF := GF))
    (h_TypedValue_Compare_ptr : typed.TypedValue.Compare_ptr.spec (GF := GF)) :
    merge.Updater.update.spec (GF := GF) := by
  sorry

end proof

end smd
end EtcdGrove
end Perennial
