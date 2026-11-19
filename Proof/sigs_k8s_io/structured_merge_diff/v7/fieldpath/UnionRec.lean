/-
`fieldpath.UnionRec`: the cluster's Löb induction.
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__UnionBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.SetNodeMap__UnionBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.UnionRec

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

/-- Löb induction over the members' bodies (with `fieldpath.UnionRec.specI`'s members read back as their
specs). -/
theorem fieldpath.UnionRec.wp_proof
    (h_Set_Union_body : fieldpath.Set.Union.specBody (GF := GF))
    (h_SetNodeMap_Union_body : fieldpath.SetNodeMap.Union.specBody (GF := GF)) :
    fieldpath.UnionRec.spec (GF := GF) := by
  have H : ⊢ fieldpath.UnionRec.specI (GF := GF) := by
    iloeb as IH
    ihave H1 := h_Set_Union_body $$ IH
    ihave H2 := h_SetNodeMap_Union_body $$ IH
    unfold fieldpath.UnionRec.specI
    isplit
    · iexact H1
    · iexact H2
  unfold fieldpath.UnionRec.specI fieldpath.Set.Union.specI fieldpath.SetNodeMap.Union.specI at H
  refine ⟨?_, ?_⟩
  · intro p p2 A B
    iintro %Φ HP HΦ
    ihave ⟨HH, -⟩ := H
    iapply HH $$ HP HΦ
  · intro p p2 A B
    iintro %Φ HP HΦ
    ihave ⟨-, HH⟩ := H
    iapply HH $$ HP HΦ

end proof

end smd
end EtcdGrove
end Perennial
