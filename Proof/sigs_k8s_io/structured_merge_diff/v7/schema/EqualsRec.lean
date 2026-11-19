/-
`schema.EqualsRec`: the cluster's Löb induction (Draft: `sorry`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.schema.Atom__EqualsBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.schema.List__EqualsBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.schema.Map__EqualsBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.schema.StructField__EqualsBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.schema.TypeRef__EqualsBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.schema.EqualsRec

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

/-- Löb induction over the members' bodies (with `schema.EqualsRec.specI`'s members read back as their
specs). -/
theorem schema.EqualsRec.wp_proof
    (h_Atom_Equals_body : schema.Atom.Equals.specBody (GF := GF))
    (h_List_Equals_body : schema.List.Equals.specBody (GF := GF))
    (h_Map_Equals_body : schema.Map.Equals.specBody (GF := GF))
    (h_StructField_Equals_body : schema.StructField.Equals.specBody (GF := GF))
    (h_TypeRef_Equals_body : schema.TypeRef.Equals.specBody (GF := GF)) :
    schema.EqualsRec.spec (GF := GF) := by
  sorry

end proof

end smd
end EtcdGrove
end Perennial
