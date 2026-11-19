/-
`typed.reconcileWithSchemaWalker.visitListItems`: not proved yet (`sorry`): the stage's Prove step, after the freeze
(notes/smd-plan.md). Draft (2026-11-19).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.reconcileWithSchemaWalker__visitListItems
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.reconcileWithSchemaWalker__prepareDescent
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.SetNodeMap__Get
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.reconcileWithSchemaWalker__reconcile
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.reconcileWithSchemaWalker__finishDescent
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.SetNodeMap__Iterate
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElementSet__Has
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElementSet__Iterate

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

theorem typed.reconcileWithSchemaWalker.visitListItems.wp_proof
    (hreconcileWithSchemaWalker_prepareDescent : typed.reconcileWithSchemaWalker.prepareDescent.spec (GF := GF))
    (hSetNodeMap_Get : fieldpath.SetNodeMap.Get.spec (GF := GF))
    (hreconcileWithSchemaWalker_reconcile : typed.reconcileWithSchemaWalker.reconcile.spec (GF := GF))
    (hreconcileWithSchemaWalker_finishDescent : typed.reconcileWithSchemaWalker.finishDescent.spec (GF := GF))
    (hSetNodeMap_Iterate : fieldpath.SetNodeMap.Iterate.spec (GF := GF))
    (hPathElementSet_Has : fieldpath.PathElementSet.Has.spec (GF := GF))
    (hPathElementSet_Iterate : fieldpath.PathElementSet.Iterate.spec (GF := GF)) :
    typed.reconcileWithSchemaWalker.visitListItems.spec (GF := GF) := by
  sorry

end proof

end smd
end EtcdGrove
end Perennial
