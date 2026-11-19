/-
`value.ListEqualsUsing`: a member of the recursion cluster `value.EqualsUsingRec` (`EqualsUsingRec.lean`); its proof is the
projection of the cluster's (its body is `ListEqualsUsingBody.lean`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.ListEqualsUsingBody
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
variable [package_sem : value.Assumptions]

theorem value.ListEqualsUsing.wp_proofBody
    (h_heapAllocator_Free : value.heapAllocator.Free.spec (GF := GF))
    (h_freelistAllocator_Free : value.freelistAllocator.Free.spec (GF := GF))
    (h_listUnstructured_Length : value.listUnstructured.Length.spec (GF := GF))
    (h_listUnstructured_Length_ptr : value.listUnstructured.Length_ptr.spec (GF := GF))
    (h_listUnstructured_RangeUsing : value.listUnstructured.RangeUsing.spec (GF := GF))
    (h_listUnstructured_RangeUsing_ptr : value.listUnstructured.RangeUsing_ptr.spec (GF := GF))
    (h_listUnstructuredRange_Item : value.listUnstructuredRange.Item.spec (GF := GF))
    (h_emptyRange_Item : value.emptyRange.Item.spec (GF := GF))
    (h_listUnstructuredRange_Next : value.listUnstructuredRange.Next.spec (GF := GF))
    (h_emptyRange_Next : value.emptyRange.Next.spec (GF := GF)) :
    value.ListEqualsUsing.specBody (GF := GF) := by
  sorry

end proof

end smd
end EtcdGrove
end Perennial
