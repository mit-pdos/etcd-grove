/-
`fieldpath.EqualsRec`: the cluster's Löb induction.
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__EqualsBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.SetNodeMap__EqualsBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.EqualsRec

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

/-- Löb induction over the members' bodies (with `fieldpath.EqualsRec.specI`'s members read back as their
specs). -/
theorem fieldpath.EqualsRec.wp_proof
    (h_Set_Equals_body : fieldpath.Set.Equals.specBody (GF := GF))
    (h_SetNodeMap_Equals_body : fieldpath.SetNodeMap.Equals.specBody (GF := GF)) :
    fieldpath.EqualsRec.spec (GF := GF) := by
  have H : ⊢ fieldpath.EqualsRec.specI (GF := GF) := by
    iloeb as IH
    ihave H1 := h_Set_Equals_body $$ IH
    ihave H2 := h_SetNodeMap_Equals_body $$ IH
    unfold fieldpath.EqualsRec.specI
    isplit
    · iexact H1
    · iexact H2
  unfold fieldpath.EqualsRec.specI fieldpath.Set.Equals.specI fieldpath.SetNodeMap.Equals.specI at H
  refine ⟨?_, ?_⟩
  · intro a0 a1 a2 a3
    iintro %Φ HP HΦ
    ihave ⟨HH, -⟩ := H
    iapply HH $$ HP HΦ
  · intro a0 a1 a2 a3
    iintro %Φ HP HΦ
    ihave ⟨-, HH⟩ := H
    iapply HH $$ HP HΦ

end proof

end smd
end EtcdGrove
end Perennial
