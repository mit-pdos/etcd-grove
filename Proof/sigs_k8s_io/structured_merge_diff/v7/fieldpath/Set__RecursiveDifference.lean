/-
`fieldpath.Set.RecursiveDifference`: not proved yet (`sorry`): Draft (notes/smd-plan.md), proved after the
freeze over its callees' specs (the hypotheses).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__RecursiveDifference
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElementSet__Difference
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElement__Less
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElementSet__Has
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__Empty

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

theorem fieldpath.Set.RecursiveDifference.wp_proof
    (wp_PathElementSet_Difference : fieldpath.PathElementSet.Difference.spec (GF := GF))
    (wp_PathElement_Less : fieldpath.PathElement.Less.spec (GF := GF))
    (wp_PathElementSet_Has : fieldpath.PathElementSet.Has.spec (GF := GF))
    (wp_Set_Empty : fieldpath.Set.Empty.spec (GF := GF)) :
    fieldpath.Set.RecursiveDifference.spec (GF := GF) := by
  sorry

end proof

end smd
end EtcdGrove
end Perennial
