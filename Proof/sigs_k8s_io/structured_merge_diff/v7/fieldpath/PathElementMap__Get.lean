/-
`fieldpath.PathElementMap.Get`: not proved yet (`sorry`): Draft (notes/smd-plan.md), proved after the
freeze over its callees' specs (the hypotheses).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElementMap__Get
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElement__Compare
public import Spec.slices.BinarySearchFunc

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

theorem fieldpath.PathElementMap.Get.wp_proof
    (wp_PathElement_Compare : fieldpath.PathElement.Compare.spec (GF := GF))
    (wp_slices_BinarySearchFunc : EtcdGrove.slices.BinarySearchFunc.spec (GF := GF)) :
    fieldpath.PathElementMap.Get.spec (GF := GF) := by
  sorry

end proof

end smd
end EtcdGrove
end Perennial
