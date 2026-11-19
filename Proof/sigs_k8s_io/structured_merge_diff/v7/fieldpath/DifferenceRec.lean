/-
`fieldpath.DifferenceRec`: the cluster's Löb induction.
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__DifferenceBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.SetNodeMap__DifferenceBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.DifferenceRec

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

/-- Löb induction over the members' bodies (with `fieldpath.DifferenceRec.specI`'s members read back as their
specs). -/
theorem fieldpath.DifferenceRec.wp_proof
    (h_Set_Difference_body : fieldpath.Set.Difference.specBody (GF := GF))
    (h_SetNodeMap_Difference_body : fieldpath.SetNodeMap.Difference.specBody (GF := GF)) :
    fieldpath.DifferenceRec.spec (GF := GF) := by
  have H : ⊢ fieldpath.DifferenceRec.specI (GF := GF) := by
    iloeb as IH
    ihave H1 := h_Set_Difference_body $$ IH
    ihave H2 := h_SetNodeMap_Difference_body $$ IH
    unfold fieldpath.DifferenceRec.specI
    isplit
    · iexact H1
    · iexact H2
  unfold fieldpath.DifferenceRec.specI fieldpath.Set.Difference.specI fieldpath.SetNodeMap.Difference.specI at H
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
