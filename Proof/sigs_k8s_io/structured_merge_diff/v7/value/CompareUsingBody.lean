/-
`value.CompareUsing`: a member of the recursion cluster `value.CompareUsingRec` (`CompareUsingRec.lean`); its proof is the
projection of the cluster's (its body is `CompareUsingBody.lean`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.CompareUsingBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.heapAllocator__Free
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.freelistAllocator__Free
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.valueUnstructured__AsBool_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.valueUnstructured__AsFloat_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.valueUnstructured__AsInt_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.valueUnstructured__AsListUsing_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.valueUnstructured__AsMapUsing_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.valueUnstructured__AsString_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.valueUnstructured__IsBool_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.valueUnstructured__IsFloat_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.valueUnstructured__IsInt_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.valueUnstructured__IsList_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.valueUnstructured__IsMap_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.valueUnstructured__IsNull_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.valueUnstructured__IsString_ptr
public import Perennial.Spec.strings.Compare
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.BoolCompare
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.FloatCompare
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.IntCompare

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

theorem value.CompareUsing.wp_proofBody
    (h_heapAllocator_Free : value.heapAllocator.Free.spec (GF := GF))
    (h_freelistAllocator_Free : value.freelistAllocator.Free.spec (GF := GF))
    (h_valueUnstructured_AsBool_ptr : value.valueUnstructured.AsBool_ptr.spec (GF := GF))
    (h_valueUnstructured_AsFloat_ptr : value.valueUnstructured.AsFloat_ptr.spec (GF := GF))
    (h_valueUnstructured_AsInt_ptr : value.valueUnstructured.AsInt_ptr.spec (GF := GF))
    (h_valueUnstructured_AsListUsing_ptr : value.valueUnstructured.AsListUsing_ptr.spec (GF := GF))
    (h_valueUnstructured_AsMapUsing_ptr : value.valueUnstructured.AsMapUsing_ptr.spec (GF := GF))
    (h_valueUnstructured_AsString_ptr : value.valueUnstructured.AsString_ptr.spec (GF := GF))
    (h_valueUnstructured_IsBool_ptr : value.valueUnstructured.IsBool_ptr.spec (GF := GF))
    (h_valueUnstructured_IsFloat_ptr : value.valueUnstructured.IsFloat_ptr.spec (GF := GF))
    (h_valueUnstructured_IsInt_ptr : value.valueUnstructured.IsInt_ptr.spec (GF := GF))
    (h_valueUnstructured_IsList_ptr : value.valueUnstructured.IsList_ptr.spec (GF := GF))
    (h_valueUnstructured_IsMap_ptr : value.valueUnstructured.IsMap_ptr.spec (GF := GF))
    (h_valueUnstructured_IsNull_ptr : value.valueUnstructured.IsNull_ptr.spec (GF := GF))
    (h_valueUnstructured_IsString_ptr : value.valueUnstructured.IsString_ptr.spec (GF := GF))
    (h_strings_Compare : _root_.Perennial.strings.Compare.spec (GF := GF))
    (h_BoolCompare : value.BoolCompare.spec (GF := GF))
    (h_FloatCompare : value.FloatCompare.spec (GF := GF))
    (h_IntCompare : value.IntCompare.spec (GF := GF)) :
    value.CompareUsing.specBody (GF := GF) := by
  sorry

end proof

end smd
end EtcdGrove
end Perennial
