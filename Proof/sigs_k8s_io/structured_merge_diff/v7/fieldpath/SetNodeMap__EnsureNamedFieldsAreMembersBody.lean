/-
`fieldpath.SetNodeMap.EnsureNamedFieldsAreMembers`: a member of the recursion cluster `fieldpath.EnsureNamedFieldsAreMembersRec` (`EnsureNamedFieldsAreMembersRec.lean`); its proof is the
projection of the cluster's (its body is `SetNodeMap__EnsureNamedFieldsAreMembersBody.lean`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.SetNodeMap__EnsureNamedFieldsAreMembersBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.SetNodeMap__Size
public import Spec.sigs_k8s_io.structured_merge_diff.v7.schema.Map__FindField
public import Spec.sigs_k8s_io.structured_merge_diff.v7.schema.Schema__Resolve
import all Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Defs
import all Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Vocab
import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofsEnsure
import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofsEnsure

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

theorem fieldpath.SetNodeMap.EnsureNamedFieldsAreMembers.wp_proofBody
    (h_SetNodeMap_Size : fieldpath.SetNodeMap.Size.spec (GF := GF))
    (h_Map_FindField : schema.Map.FindField.spec (GF := GF))
    (h_Schema_Resolve : schema.Schema.Resolve.spec (GF := GF)) :
    fieldpath.SetNodeMap.EnsureNamedFieldsAreMembers.specBody (GF := GF) := by
  unfold fieldpath.SetNodeMap.EnsureNamedFieldsAreMembers.specBody fieldpath.EnsureNamedFieldsAreMembersRec.specI
    fieldpath.Set.EnsureNamedFieldsAreMembers.specI fieldpath.SetNodeMap.EnsureNamedFieldsAreMembers.specI
  iintro #IH
  iintro %l %D %sc %S %tr %ty
  wp_start as ⟨#Hl, #Hsc, #Htr, %hpre⟩
  wp_auto
  wp_apply (h_SetNodeMap_Size l D) $$ [$Hl] as %sz %hsz
  trace_state
  sorry

end proof

end smd
end EtcdGrove
end Perennial
