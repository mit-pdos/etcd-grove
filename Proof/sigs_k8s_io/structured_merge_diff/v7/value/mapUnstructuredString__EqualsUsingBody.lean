/-
`value.mapUnstructuredString.EqualsUsing`: a member of the recursion cluster `value.EqualsUsingRec` (`EqualsUsingRec.lean`); its proof is the
projection of the cluster's (its body is `mapUnstructuredString__EqualsUsingBody.lean`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.mapUnstructuredString__EqualsUsingBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.heapAllocator__Free
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.freelistAllocator__Free
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.heapAllocator__allocValueUnstructured
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.freelistAllocator__allocValueUnstructured
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.mapUnstructuredString__IterateUsing
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.mapUnstructuredString__Length
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.valueUnstructured__reuse

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

theorem value.mapUnstructuredString.EqualsUsing.wp_proofBody
    (h_heapAllocator_Free : value.heapAllocator.Free.spec (GF := GF))
    (h_freelistAllocator_Free : value.freelistAllocator.Free.spec (GF := GF))
    (h_heapAllocator_allocValueUnstructured : value.heapAllocator.allocValueUnstructured.spec (GF := GF))
    (h_freelistAllocator_allocValueUnstructured : value.freelistAllocator.allocValueUnstructured.spec (GF := GF))
    (h_mapUnstructuredString_IterateUsing : value.mapUnstructuredString.IterateUsing.spec (GF := GF))
    (h_mapUnstructuredString_Length : value.mapUnstructuredString.Length.spec (GF := GF))
    (h_valueUnstructured_reuse : value.valueUnstructured.reuse.spec (GF := GF)) :
    value.mapUnstructuredString.EqualsUsing.specBody (GF := GF) := by
  sorry

end proof

end smd
end EtcdGrove
end Perennial
