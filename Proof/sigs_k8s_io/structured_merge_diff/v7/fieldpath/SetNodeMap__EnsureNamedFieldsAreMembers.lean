/-
`fieldpath.SetNodeMap.EnsureNamedFieldsAreMembers`: not proved yet (`sorry`): Draft (notes/smd-plan.md), proved after the
freeze over its callees' specs (the hypotheses).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.SetNodeMap__EnsureNamedFieldsAreMembers
public import Spec.sigs_k8s_io.structured_merge_diff.v7.schema.Schema__Resolve
public import Spec.sigs_k8s_io.structured_merge_diff.v7.schema.Map__FindField
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.SetNodeMap__Size
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__EnsureNamedFieldsAreMembers

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

theorem fieldpath.SetNodeMap.EnsureNamedFieldsAreMembers.wp_proof
    (wp_schema_Schema_Resolve : schema.Schema.Resolve.spec (GF := GF))
    (wp_schema_Map_FindField : schema.Map.FindField.spec (GF := GF))
    (wp_SetNodeMap_Size : fieldpath.SetNodeMap.Size.spec (GF := GF))
    (wp_Set_EnsureNamedFieldsAreMembers : fieldpath.Set.EnsureNamedFieldsAreMembers.spec (GF := GF)) :
    fieldpath.SetNodeMap.EnsureNamedFieldsAreMembers.spec (GF := GF) := by
  sorry

end proof

end smd
end EtcdGrove
end Perennial
