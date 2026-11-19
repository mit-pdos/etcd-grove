/-
`typed.ReconcileFieldSetWithSchema`: not proved yet (`sorry`): the stage's Prove step, after the freeze
(notes/smd-plan.md). Draft (2026-11-19).

Callees without a spec file here (other packages', the standard library's, or the
walker's own interface calls through a bundle): `fmt.Errorf`.
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.ReconcileFieldSetWithSchema
public import Perennial.Spec.sync.Pool__Get
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.reconcileWithSchemaWalker__reconcile
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.reconcileWithSchemaWalker__finished
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__RecursiveDifference
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__Union
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.ValidationErrors__Error

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
variable [package_sem : typed.Assumptions]

theorem typed.ReconcileFieldSetWithSchema.wp_proof
    (hPool_Get : sync.Pool.Get.spec (GF := GF))
    (hreconcileWithSchemaWalker_reconcile : typed.reconcileWithSchemaWalker.reconcile.spec (GF := GF))
    (hreconcileWithSchemaWalker_finished : typed.reconcileWithSchemaWalker.finished.spec (GF := GF))
    (hSet_RecursiveDifference : fieldpath.Set.RecursiveDifference.spec (GF := GF))
    (hSet_Union : fieldpath.Set.Union.spec (GF := GF))
    (hValidationErrors_Error : typed.ValidationErrors.Error.spec (GF := GF)) :
    typed.ReconcileFieldSetWithSchema.spec (GF := GF) := by
  sorry

end proof

end smd
end EtcdGrove
end Perennial
