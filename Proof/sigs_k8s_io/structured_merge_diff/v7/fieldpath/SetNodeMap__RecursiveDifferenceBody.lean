/-
`fieldpath.SetNodeMap.RecursiveDifference`: a member of the recursion cluster `fieldpath.RecursiveDifferenceRec` (`RecursiveDifferenceRec.lean`); its proof is the
projection of the cluster's (its body is `SetNodeMap__RecursiveDifferenceBody.lean`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.SetNodeMap__RecursiveDifferenceBody
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

theorem fieldpath.SetNodeMap.RecursiveDifference.wp_proofBody
    (h_PathElement_Less : fieldpath.PathElement.Less.spec (GF := GF))
    (h_PathElementSet_Has : fieldpath.PathElementSet.Has.spec (GF := GF))
    (h_Set_Empty : fieldpath.Set.Empty.spec (GF := GF)) :
    fieldpath.SetNodeMap.RecursiveDifference.specBody (GF := GF) := by
  sorry

end proof

end smd
end EtcdGrove
end Perennial
