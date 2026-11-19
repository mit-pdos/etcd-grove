/-
`typed.reconcileWithSchemaWalkerRec`: the cluster's Löb induction (Draft: `sorry`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.reconcileWithSchemaWalker__doListBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.reconcileWithSchemaWalker__doMapBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.reconcileWithSchemaWalker__reconcileBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.reconcileWithSchemaWalker__visitListItemsBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.reconcileWithSchemaWalker__visitMapItemsBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.reconcileWithSchemaWalkerRec

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

/-- Löb induction over the members' bodies (with `typed.reconcileWithSchemaWalkerRec.specI`'s members read back as their
specs). -/
theorem typed.reconcileWithSchemaWalkerRec.wp_proof
    (h_reconcileWithSchemaWalker_doList_body : typed.reconcileWithSchemaWalker.doList.specBody (GF := GF))
    (h_reconcileWithSchemaWalker_doMap_body : typed.reconcileWithSchemaWalker.doMap.specBody (GF := GF))
    (h_reconcileWithSchemaWalker_reconcile_body : typed.reconcileWithSchemaWalker.reconcile.specBody (GF := GF))
    (h_reconcileWithSchemaWalker_visitListItems_body : typed.reconcileWithSchemaWalker.visitListItems.specBody (GF := GF))
    (h_reconcileWithSchemaWalker_visitMapItems_body : typed.reconcileWithSchemaWalker.visitMapItems.specBody (GF := GF)) :
    typed.reconcileWithSchemaWalkerRec.spec (GF := GF) := by
  sorry

end proof

end smd
end EtcdGrove
end Perennial
