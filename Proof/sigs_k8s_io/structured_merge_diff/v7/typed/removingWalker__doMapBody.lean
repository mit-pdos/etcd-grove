/-
`typed.removingWalker.doMap`: a member of the recursion cluster `typed.removingWalkerRec` (`removingWalkerRec.lean`); its proof is the
projection of the cluster's (its body is `removingWalker__doMapBody.lean`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.removingWalker__doMapBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.MakePath
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__Empty
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__Has
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__WithPrefix
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.heapAllocator__Free
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.freelistAllocator__Free
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.mapUnstructuredString__Empty
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.mapUnstructuredString__Iterate
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.valueUnstructured__AsMapUsing_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.valueUnstructured__IsMap_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.valueUnstructured__Unstructured_ptr

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

theorem typed.removingWalker.doMap.wp_proofBody
    (h_MakePath : fieldpath.MakePath.spec (GF := GF))
    (h_Set_Empty : fieldpath.Set.Empty.spec (GF := GF))
    (h_Set_Has : fieldpath.Set.Has.spec (GF := GF))
    (h_Set_WithPrefix : fieldpath.Set.WithPrefix.spec (GF := GF))
    (h_heapAllocator_Free : value.heapAllocator.Free.spec (GF := GF))
    (h_freelistAllocator_Free : value.freelistAllocator.Free.spec (GF := GF))
    (h_mapUnstructuredString_Empty : value.mapUnstructuredString.Empty.spec (GF := GF))
    (h_mapUnstructuredString_Iterate : value.mapUnstructuredString.Iterate.spec (GF := GF))
    (h_valueUnstructured_AsMapUsing_ptr : value.valueUnstructured.AsMapUsing_ptr.spec (GF := GF))
    (h_valueUnstructured_IsMap_ptr : value.valueUnstructured.IsMap_ptr.spec (GF := GF))
    (h_valueUnstructured_Unstructured_ptr : value.valueUnstructured.Unstructured_ptr.spec (GF := GF)) :
    typed.removingWalker.doMap.specBody (GF := GF) := by
  sorry

end proof

end smd
end EtcdGrove
end Perennial
