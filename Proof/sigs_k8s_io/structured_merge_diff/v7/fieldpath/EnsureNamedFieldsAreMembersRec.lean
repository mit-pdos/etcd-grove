/-
`fieldpath.EnsureNamedFieldsAreMembersRec`: the cluster's Löb induction (Draft: `sorry`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__EnsureNamedFieldsAreMembersBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.SetNodeMap__EnsureNamedFieldsAreMembersBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.EnsureNamedFieldsAreMembersRec

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

/-- Löb induction over the members' bodies (with `fieldpath.EnsureNamedFieldsAreMembersRec.specI`'s members read back as their
specs). -/
theorem fieldpath.EnsureNamedFieldsAreMembersRec.wp_proof
    (h_Set_EnsureNamedFieldsAreMembers_body : fieldpath.Set.EnsureNamedFieldsAreMembers.specBody (GF := GF))
    (h_SetNodeMap_EnsureNamedFieldsAreMembers_body : fieldpath.SetNodeMap.EnsureNamedFieldsAreMembers.specBody (GF := GF)) :
    fieldpath.EnsureNamedFieldsAreMembersRec.spec (GF := GF) := by
  sorry

end proof

end smd
end EtcdGrove
end Perennial
