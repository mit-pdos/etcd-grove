/-
`fieldpath.SetNodeMap.Union`: a member of the recursion cluster `fieldpath.UnionRec` (`UnionRec.lean`); its proof is the
projection of the cluster's (its body is `SetNodeMap__UnionBody.lean`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.SetNodeMap__UnionBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElement__Less

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

theorem fieldpath.SetNodeMap.Union.wp_proofBody
    (h_PathElement_Less : fieldpath.PathElement.Less.spec (GF := GF)) :
    fieldpath.SetNodeMap.Union.specBody (GF := GF) := by
  sorry

end proof

end smd
end EtcdGrove
end Perennial
