/-
`merge.Updater.Apply`: not proved yet (`sorry`): the stage's Prove step, after the freeze
(notes/smd-plan.md). Lean-first (2026-11-19).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.merge.Updater__Apply
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.NewVersionedSet
public import Spec.sigs_k8s_io.structured_merge_diff.v7.merge.Updater__prune
public import Spec.sigs_k8s_io.structured_merge_diff.v7.merge.Updater__reconcileManagedFieldsWithSchemaChanges
public import Spec.sigs_k8s_io.structured_merge_diff.v7.merge.Updater__update
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.TypedValue__AsValue_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.TypedValue__Merge_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.TypedValue__ToFieldSet_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.EqualsUsing
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.NewFreelistAllocator

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

theorem merge.Updater.Apply.wp_proof
    (h_NewVersionedSet : fieldpath.NewVersionedSet.spec (GF := GF))
    (h_Updater_prune : merge.Updater.prune.spec (GF := GF))
    (h_Updater_reconcileManagedFieldsWithSchemaChanges : merge.Updater.reconcileManagedFieldsWithSchemaChanges.spec (GF := GF))
    (h_Updater_update : merge.Updater.update.spec (GF := GF))
    (h_TypedValue_AsValue_ptr : typed.TypedValue.AsValue_ptr.spec (GF := GF))
    (h_TypedValue_Merge_ptr : typed.TypedValue.Merge_ptr.spec (GF := GF))
    (h_TypedValue_ToFieldSet_ptr : typed.TypedValue.ToFieldSet_ptr.spec (GF := GF))
    (h_EqualsUsing : value.EqualsUsing.spec (GF := GF))
    (h_NewFreelistAllocator : value.NewFreelistAllocator.spec (GF := GF)) :
    merge.Updater.Apply.spec (GF := GF) := by
  sorry

end proof

end smd
end EtcdGrove
end Perennial
