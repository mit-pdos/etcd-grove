/-
`typed.toFieldSetWalker.visitMapItems`: a member of the recursion cluster `typed.toFieldSetWalkerRec` (`toFieldSetWalkerRec.lean`); its proof is the
projection of the cluster's (its body is `toFieldSetWalker__visitMapItemsBody.lean`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.toFieldSetWalker__visitMapItemsBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__Insert
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.mapUnstructuredString__Iterate
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.mapUnstructuredString__Length
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.valueUnstructured__AsMap_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.valueUnstructured__IsMap_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.valueUnstructured__IsNull_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.schema.Map__FindField
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.toFieldSetWalker__finishDescent
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.toFieldSetWalker__prepareDescent

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

theorem typed.toFieldSetWalker.visitMapItems.wp_proofBody
    (h_Set_Insert : fieldpath.Set.Insert.spec (GF := GF))
    (h_mapUnstructuredString_Iterate : value.mapUnstructuredString.Iterate.spec (GF := GF))
    (h_mapUnstructuredString_Length : value.mapUnstructuredString.Length.spec (GF := GF))
    (h_valueUnstructured_AsMap_ptr : value.valueUnstructured.AsMap_ptr.spec (GF := GF))
    (h_valueUnstructured_IsMap_ptr : value.valueUnstructured.IsMap_ptr.spec (GF := GF))
    (h_valueUnstructured_IsNull_ptr : value.valueUnstructured.IsNull_ptr.spec (GF := GF))
    (h_Map_FindField : schema.Map.FindField.spec (GF := GF))
    (h_toFieldSetWalker_finishDescent : typed.toFieldSetWalker.finishDescent.spec (GF := GF))
    (h_toFieldSetWalker_prepareDescent : typed.toFieldSetWalker.prepareDescent.spec (GF := GF)) :
    typed.toFieldSetWalker.visitMapItems.specBody (GF := GF) := by
  sorry

end proof

end smd
end EtcdGrove
end Perennial
