/-
`value.EqualsUsingRec`: the cluster's Löb induction (Draft: `sorry`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.EqualsUsingBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.ListEqualsUsingBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.listUnstructured__EqualsUsingBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.listUnstructured__EqualsUsing_ptrBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.mapUnstructuredString__EqualsUsingBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.EqualsUsingRec

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

/-- Löb induction over the members' bodies (with `value.EqualsUsingRec.specI`'s members read back as their
specs). -/
theorem value.EqualsUsingRec.wp_proof
    (h_EqualsUsing_body : value.EqualsUsing.specBody (GF := GF))
    (h_ListEqualsUsing_body : value.ListEqualsUsing.specBody (GF := GF))
    (h_listUnstructured_EqualsUsing_body : value.listUnstructured.EqualsUsing.specBody (GF := GF))
    (h_listUnstructured_EqualsUsing_ptr_body : value.listUnstructured.EqualsUsing_ptr.specBody (GF := GF))
    (h_mapUnstructuredString_EqualsUsing_body : value.mapUnstructuredString.EqualsUsing.specBody (GF := GF)) :
    value.EqualsUsingRec.spec (GF := GF) := by
  sorry

end proof

end smd
end EtcdGrove
end Perennial
