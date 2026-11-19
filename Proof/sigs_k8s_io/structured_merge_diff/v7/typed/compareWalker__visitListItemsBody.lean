/-
`typed.compareWalker.visitListItems`: a member of the recursion cluster `typed.compareWalkerRec` (`compareWalkerRec.lean`); its proof is the
projection of the cluster's (its body is `compareWalker__visitListItemsBody.lean`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.compareWalker__visitListItemsBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.MakePathElementMap
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElementMap__Get
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElementMap__Insert
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__Insert
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.listUnstructured__At
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.listUnstructured__At_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.listUnstructured__Length
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.listUnstructured__Length_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.listItemToPathElement
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.Equals

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

theorem typed.compareWalker.visitListItems.wp_proofBody
    (h_MakePathElementMap : fieldpath.MakePathElementMap.spec (GF := GF))
    (h_PathElementMap_Get : fieldpath.PathElementMap.Get.spec (GF := GF))
    (h_PathElementMap_Insert : fieldpath.PathElementMap.Insert.spec (GF := GF))
    (h_Set_Insert : fieldpath.Set.Insert.spec (GF := GF))
    (h_listUnstructured_At : value.listUnstructured.At.spec (GF := GF))
    (h_listUnstructured_At_ptr : value.listUnstructured.At_ptr.spec (GF := GF))
    (h_listUnstructured_Length : value.listUnstructured.Length.spec (GF := GF))
    (h_listUnstructured_Length_ptr : value.listUnstructured.Length_ptr.spec (GF := GF))
    (h_listItemToPathElement : typed.listItemToPathElement.spec (GF := GF))
    (h_Equals : value.Equals.spec (GF := GF)) :
    typed.compareWalker.visitListItems.specBody (GF := GF) := by
  sorry

end proof

end smd
end EtcdGrove
end Perennial
