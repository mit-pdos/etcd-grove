/-
`schema.StructField.Equals`: a member of the recursion cluster `schema.EqualsRec` (`EqualsRec.lean`); its proof is the
projection of the cluster's (its body is `StructField__EqualsBody.lean`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.schema.StructField__EqualsBody
public import Spec.reflect.DeepEqualNil

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
variable [package_sem : schema.Assumptions]

theorem schema.StructField.Equals.wp_proofBody
    (h_reflect_DeepEqual_Nil : _root_.Perennial.EtcdGrove.reflect.DeepEqual.specNil (GF := GF) (hG := hG)) :
    schema.StructField.Equals.specBody (GF := GF) := by
  sorry

end proof

end smd
end EtcdGrove
end Perennial
