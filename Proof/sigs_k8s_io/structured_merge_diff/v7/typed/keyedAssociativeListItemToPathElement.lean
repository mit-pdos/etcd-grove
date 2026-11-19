/-
`typed.keyedAssociativeListItemToPathElement`: not proved yet (`sorry`): the stage's Prove step, after the freeze
(notes/smd-plan.md). Draft (2026-11-19).

Callees without a spec file here (other packages', the standard library's, or the
walker's own interface calls through a bundle): `errors.New`, `fmt.Errorf`.
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.keyedAssociativeListItemToPathElement
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.heapAllocator__Free
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.freelistAllocator__Free
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.mapUnstructuredString__Get
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.valueUnstructured__AsMapUsing_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.valueUnstructured__IsMap_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.valueUnstructured__IsNull_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.getAssociativeKeyDefault
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.FieldList__Sort
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.NewValueInterface

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

theorem typed.keyedAssociativeListItemToPathElement.wp_proof
    (h_heapAllocator_Free : value.heapAllocator.Free.spec (GF := GF))
    (h_freelistAllocator_Free : value.freelistAllocator.Free.spec (GF := GF))
    (h_mapUnstructuredString_Get : value.mapUnstructuredString.Get.spec (GF := GF))
    (h_valueUnstructured_AsMapUsing_ptr : value.valueUnstructured.AsMapUsing_ptr.spec (GF := GF))
    (h_valueUnstructured_IsMap_ptr : value.valueUnstructured.IsMap_ptr.spec (GF := GF))
    (h_valueUnstructured_IsNull_ptr : value.valueUnstructured.IsNull_ptr.spec (GF := GF))
    (h_getAssociativeKeyDefault : typed.getAssociativeKeyDefault.spec (GF := GF))
    (h_FieldList_Sort : value.FieldList.Sort.spec (GF := GF))
    (h_NewValueInterface : value.NewValueInterface.spec (GF := GF)) :
    typed.keyedAssociativeListItemToPathElement.spec (GF := GF) := by
  sorry

end proof

end smd
end EtcdGrove
end Perennial
