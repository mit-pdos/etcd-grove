/-
`typed.removingWalker.doList`: a member of the recursion cluster `typed.removingWalkerRec` (`removingWalkerRec.lean`); its proof is the
projection of the cluster's (its body is `removingWalker__doListBody.lean`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.removingWalker__doListBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.MakePath
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__Empty
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__Has
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__WithPrefix
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.heapAllocator__Free
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.freelistAllocator__Free
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.listUnstructured__Length
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.listUnstructured__Length_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.listUnstructured__RangeUsing
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.listUnstructured__RangeUsing_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.listUnstructuredRange__Item
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.emptyRange__Item
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.listUnstructuredRange__Next
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.emptyRange__Next
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.valueUnstructured__AsListUsing_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.valueUnstructured__IsList_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.valueUnstructured__Unstructured_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.listItemToPathElement

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

theorem typed.removingWalker.doList.wp_proofBody
    (h_MakePath : fieldpath.MakePath.spec (GF := GF))
    (h_Set_Empty : fieldpath.Set.Empty.spec (GF := GF))
    (h_Set_Has : fieldpath.Set.Has.spec (GF := GF))
    (h_Set_WithPrefix : fieldpath.Set.WithPrefix.spec (GF := GF))
    (h_heapAllocator_Free : value.heapAllocator.Free.spec (GF := GF))
    (h_freelistAllocator_Free : value.freelistAllocator.Free.spec (GF := GF))
    (h_listUnstructured_Length : value.listUnstructured.Length.spec (GF := GF))
    (h_listUnstructured_Length_ptr : value.listUnstructured.Length_ptr.spec (GF := GF))
    (h_listUnstructured_RangeUsing : value.listUnstructured.RangeUsing.spec (GF := GF))
    (h_listUnstructured_RangeUsing_ptr : value.listUnstructured.RangeUsing_ptr.spec (GF := GF))
    (h_listUnstructuredRange_Item : value.listUnstructuredRange.Item.spec (GF := GF))
    (h_emptyRange_Item : value.emptyRange.Item.spec (GF := GF))
    (h_listUnstructuredRange_Next : value.listUnstructuredRange.Next.spec (GF := GF))
    (h_emptyRange_Next : value.emptyRange.Next.spec (GF := GF))
    (h_valueUnstructured_AsListUsing_ptr : value.valueUnstructured.AsListUsing_ptr.spec (GF := GF))
    (h_valueUnstructured_IsList_ptr : value.valueUnstructured.IsList_ptr.spec (GF := GF))
    (h_valueUnstructured_Unstructured_ptr : value.valueUnstructured.Unstructured_ptr.spec (GF := GF))
    (h_listItemToPathElement : typed.listItemToPathElement.spec (GF := GF)) :
    typed.removingWalker.doList.specBody (GF := GF) := by
  sorry

end proof

end smd
end EtcdGrove
end Perennial
