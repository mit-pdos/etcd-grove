/-
`typed.mergingWalker.visitListItems`: not proved yet (`sorry`): the stage's Prove step, after the freeze
(notes/smd-plan.md). Draft (2026-11-19).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.mergingWalker__visitListItems
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.mergingWalker__indexListPathElements
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.MakePathElementMap
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElementMap__Insert
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElementMap__Get
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElementValueMap__Get
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElement__Equals
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.mergingWalker__mergeListItem

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

theorem typed.mergingWalker.visitListItems.wp_proof
    (hmergingWalker_indexListPathElements : typed.mergingWalker.indexListPathElements.spec (GF := GF))
    (hMakePathElementMap : fieldpath.MakePathElementMap.spec (GF := GF))
    (hPathElementMap_Insert : fieldpath.PathElementMap.Insert.spec (GF := GF))
    (hPathElementMap_Get : fieldpath.PathElementMap.Get.spec (GF := GF))
    (hPathElementValueMap_Get : fieldpath.PathElementValueMap.Get.spec (GF := GF))
    (hPathElement_Equals : fieldpath.PathElement.Equals.spec (GF := GF))
    (hmergingWalker_mergeListItem : typed.mergingWalker.mergeListItem.spec (GF := GF)) :
    typed.mergingWalker.visitListItems.spec (GF := GF) := by
  sorry

end proof

end smd
end EtcdGrove
end Perennial
