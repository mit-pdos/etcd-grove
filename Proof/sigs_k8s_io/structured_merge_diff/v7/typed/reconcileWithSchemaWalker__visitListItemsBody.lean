/-
`typed.reconcileWithSchemaWalker.visitListItems`: a member of the recursion cluster `typed.reconcileWithSchemaWalkerRec` (`reconcileWithSchemaWalkerRec.lean`); its proof is the
projection of the cluster's (its body is `reconcileWithSchemaWalker__visitListItemsBody.lean`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.reconcileWithSchemaWalker__visitListItemsBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElementSet__Has
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElementSet__Iterate
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.SetNodeMap__Get
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.SetNodeMap__Iterate
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.reconcileWithSchemaWalker__finishDescent
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.reconcileWithSchemaWalker__prepareDescent

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

theorem typed.reconcileWithSchemaWalker.visitListItems.wp_proofBody
    (h_PathElementSet_Has : fieldpath.PathElementSet.Has.spec (GF := GF))
    (h_PathElementSet_Iterate : fieldpath.PathElementSet.Iterate.spec (GF := GF))
    (h_SetNodeMap_Get : fieldpath.SetNodeMap.Get.spec (GF := GF))
    (h_SetNodeMap_Iterate : fieldpath.SetNodeMap.Iterate.spec (GF := GF))
    (h_reconcileWithSchemaWalker_finishDescent : typed.reconcileWithSchemaWalker.finishDescent.spec (GF := GF))
    (h_reconcileWithSchemaWalker_prepareDescent : typed.reconcileWithSchemaWalker.prepareDescent.spec (GF := GF)) :
    typed.reconcileWithSchemaWalker.visitListItems.specBody (GF := GF) := by
  sorry

end proof

end smd
end EtcdGrove
end Perennial
