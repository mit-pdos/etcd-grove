/-
`typed.compareWalkerRec`: the cluster's Löb induction (Draft: `sorry`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.compareWalker__compareBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.compareWalker__compareListItemBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.compareWalker__doListBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.compareWalker__doMapBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.compareWalker__visitListItemsBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.compareWalker__visitMapItemBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.compareWalker__visitMapItemsBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.compareWalkerRec

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

/-- Löb induction over the members' bodies (with `typed.compareWalkerRec.specI`'s members read back as their
specs). -/
theorem typed.compareWalkerRec.wp_proof
    (h_compareWalker_compare_body : typed.compareWalker.compare.specBody (GF := GF))
    (h_compareWalker_compareListItem_body : typed.compareWalker.compareListItem.specBody (GF := GF))
    (h_compareWalker_doList_body : typed.compareWalker.doList.specBody (GF := GF))
    (h_compareWalker_doMap_body : typed.compareWalker.doMap.specBody (GF := GF))
    (h_compareWalker_visitListItems_body : typed.compareWalker.visitListItems.specBody (GF := GF))
    (h_compareWalker_visitMapItem_body : typed.compareWalker.visitMapItem.specBody (GF := GF))
    (h_compareWalker_visitMapItems_body : typed.compareWalker.visitMapItems.specBody (GF := GF)) :
    typed.compareWalkerRec.spec (GF := GF) := by
  sorry

end proof

end smd
end EtcdGrove
end Perennial
