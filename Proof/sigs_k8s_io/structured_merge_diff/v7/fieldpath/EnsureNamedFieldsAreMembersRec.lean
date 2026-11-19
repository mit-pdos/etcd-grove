/-
`fieldpath.EnsureNamedFieldsAreMembersRec`: the cluster's Löb induction.
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
  have H : ⊢ fieldpath.EnsureNamedFieldsAreMembersRec.specI (GF := GF) := by
    iloeb as IH
    ihave H1 := h_Set_EnsureNamedFieldsAreMembers_body $$ IH
    ihave H2 := h_SetNodeMap_EnsureNamedFieldsAreMembers_body $$ IH
    unfold fieldpath.EnsureNamedFieldsAreMembersRec.specI
    isplit
    · iexact H1
    · iexact H2
  unfold fieldpath.EnsureNamedFieldsAreMembersRec.specI fieldpath.Set.EnsureNamedFieldsAreMembers.specI fieldpath.SetNodeMap.EnsureNamedFieldsAreMembers.specI at H
  refine ⟨?_, ?_⟩
  · intro a0 a1 a2 a3 a4 a5
    iintro %Φ HP HΦ
    ihave ⟨HH, -⟩ := H
    iapply HH $$ HP HΦ
  · intro a0 a1 a2 a3 a4 a5
    iintro %Φ HP HΦ
    ihave ⟨-, HH⟩ := H
    iapply HH $$ HP HΦ

end proof

end smd
end EtcdGrove
end Perennial
