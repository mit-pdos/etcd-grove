/-
`typed.mergingWalker.visitListItems`: a member of the recursion cluster `typed.mergingWalkerRec` (`mergingWalkerRec.lean`); its proof is the
projection of the cluster's (its body is `mergingWalker__visitListItemsBody.lean`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.mergingWalker__visitListItemsBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.MakePathElementMap
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElement__Equals
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElementMap__Get
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElementMap__Insert
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElementValueMap__Get
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.listUnstructured__AtUsing
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.listUnstructured__AtUsing_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.listUnstructured__Length
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.listUnstructured__Length_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.mergingWalker__indexListPathElements

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

theorem typed.mergingWalker.visitListItems.wp_proofBody
    (h_MakePathElementMap : fieldpath.MakePathElementMap.spec (GF := GF))
    (h_PathElement_Equals : fieldpath.PathElement.Equals.spec (GF := GF))
    (h_PathElementMap_Get : fieldpath.PathElementMap.Get.spec (GF := GF))
    (h_PathElementMap_Insert : fieldpath.PathElementMap.Insert.spec (GF := GF))
    (h_PathElementValueMap_Get : fieldpath.PathElementValueMap.Get.spec (GF := GF))
    (h_listUnstructured_AtUsing : value.listUnstructured.AtUsing.spec (GF := GF))
    (h_listUnstructured_AtUsing_ptr : value.listUnstructured.AtUsing_ptr.spec (GF := GF))
    (h_listUnstructured_Length : value.listUnstructured.Length.spec (GF := GF))
    (h_listUnstructured_Length_ptr : value.listUnstructured.Length_ptr.spec (GF := GF))
    (h_mergingWalker_indexListPathElements : typed.mergingWalker.indexListPathElements.spec (GF := GF)) :
    typed.mergingWalker.visitListItems.specBody (GF := GF) := by
  sorry

end proof

end smd
end EtcdGrove
end Perennial
