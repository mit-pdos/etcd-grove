/-
`fieldpath.Set.EnsureNamedFieldsAreMembers`: not proved yet (`sorry`): Draft (notes/smd-plan.md), proved after the
freeze over its callees' specs (the hypotheses).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__EnsureNamedFieldsAreMembers
public import Spec.sigs_k8s_io.structured_merge_diff.v7.schema.Schema__Resolve
public import Spec.sigs_k8s_io.structured_merge_diff.v7.schema.Map__FindField
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElementSet__Size
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElementSet__Insert
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.SetNodeMap__Size

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

theorem fieldpath.Set.EnsureNamedFieldsAreMembers.wp_proof
    (wp_schema_Schema_Resolve : schema.Schema.Resolve.spec (GF := GF))
    (wp_schema_Map_FindField : schema.Map.FindField.spec (GF := GF))
    (wp_PathElementSet_Size : fieldpath.PathElementSet.Size.spec (GF := GF))
    (wp_PathElementSet_Insert : fieldpath.PathElementSet.Insert.spec (GF := GF))
    (wp_SetNodeMap_Size : fieldpath.SetNodeMap.Size.spec (GF := GF)) :
    fieldpath.Set.EnsureNamedFieldsAreMembers.spec (GF := GF) := by
  sorry

end proof

end smd
end EtcdGrove
end Perennial
