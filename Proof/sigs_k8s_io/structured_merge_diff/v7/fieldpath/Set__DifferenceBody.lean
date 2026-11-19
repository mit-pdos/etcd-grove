/-
`fieldpath.Set.Difference`: a member of the recursion cluster `fieldpath.DifferenceRec` (`DifferenceRec.lean`); its proof is the
projection of the cluster's (its body is `Set__DifferenceBody.lean`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__DifferenceBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElementSet__Difference

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

theorem fieldpath.Set.Difference.wp_proofBody
    (h_PathElementSet_Difference : fieldpath.PathElementSet.Difference.spec (GF := GF)) :
    fieldpath.Set.Difference.specBody (GF := GF) := by
  sorry

end proof

end smd
end EtcdGrove
end Perennial
