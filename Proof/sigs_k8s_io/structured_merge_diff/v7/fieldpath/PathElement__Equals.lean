/-
`fieldpath.PathElement.Equals`: not proved yet (`sorry`): Draft (notes/smd-plan.md), proved after the
freeze over its callees' specs (the hypotheses).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElement__Equals
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.Equals
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.FieldList__Equals

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
variable [package_sem : fieldpath.Assumptions]

theorem fieldpath.PathElement.Equals.wp_proof
    (h_Equals : value.Equals.spec (GF := GF))
    (h_FieldList_Equals : value.FieldList.Equals.spec (GF := GF)) :
    fieldpath.PathElement.Equals.spec (GF := GF) := by
  sorry

end proof

end smd
end EtcdGrove
end Perennial
