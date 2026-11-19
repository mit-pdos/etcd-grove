/-
`typed.mergingWalkerRec`: the cluster's Löb induction (Draft: `sorry`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.mergingWalker__doListBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.mergingWalker__doMapBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.mergingWalker__mergeBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.mergingWalker__mergeListItemBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.mergingWalker__visitListItemsBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.mergingWalker__visitMapItemBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.mergingWalker__visitMapItemsBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.mergingWalkerRec

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

/-- Löb induction over the members' bodies (with `typed.mergingWalkerRec.specI`'s members read back as their
specs). -/
theorem typed.mergingWalkerRec.wp_proof
    (h_mergingWalker_doList_body : typed.mergingWalker.doList.specBody (GF := GF))
    (h_mergingWalker_doMap_body : typed.mergingWalker.doMap.specBody (GF := GF))
    (h_mergingWalker_merge_body : typed.mergingWalker.merge.specBody (GF := GF))
    (h_mergingWalker_mergeListItem_body : typed.mergingWalker.mergeListItem.specBody (GF := GF))
    (h_mergingWalker_visitListItems_body : typed.mergingWalker.visitListItems.specBody (GF := GF))
    (h_mergingWalker_visitMapItem_body : typed.mergingWalker.visitMapItem.specBody (GF := GF))
    (h_mergingWalker_visitMapItems_body : typed.mergingWalker.visitMapItems.specBody (GF := GF)) :
    typed.mergingWalkerRec.spec (GF := GF) := by
  sorry

end proof

end smd
end EtcdGrove
end Perennial
