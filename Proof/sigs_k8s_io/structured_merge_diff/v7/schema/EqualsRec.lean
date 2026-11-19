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
  have H : ⊢ schema.EqualsRec.specI (GF := GF) := by
    iloeb as IH
    ihave H1 := h_Atom_Equals_body $$ IH
    ihave H2 := h_List_Equals_body $$ IH
    ihave H3 := h_Map_Equals_body $$ IH
    ihave H4 := h_StructField_Equals_body $$ IH
    ihave H5 := h_TypeRef_Equals_body $$ IH
    unfold schema.EqualsRec.specI
    isplit
    · iexact H1
    isplit
    · iexact H2
    isplit
    · iexact H3
    isplit
    · iexact H4
    · iexact H5
  unfold schema.EqualsRec.specI schema.Atom.Equals.specI schema.List.Equals.specI
    schema.Map.Equals.specI schema.StructField.Equals.specI schema.TypeRef.Equals.specI at H
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a0 a1 a2 a3 a4 a5 a6 a7
    iintro %Φ HP HΦ
    ihave ⟨HH, -⟩ := H
    iapply HH $$ HP HΦ
  · intro a0 a1 a2 a3 a4 a5 a6 a7
    iintro %Φ HP HΦ
    ihave ⟨-, HH, -⟩ := H
    iapply HH $$ HP HΦ
  · intro a0 a1 a2 a3 a4 a5 a6 a7
    iintro %Φ HP HΦ
    ihave ⟨-, -, HH, -⟩ := H
    iapply HH $$ HP HΦ
  · intro a0 a1 a2 a3 a4 a5 a6 a7
    iintro %Φ HP HΦ
    ihave ⟨-, -, -, HH, -⟩ := H
    iapply HH $$ HP HΦ
  · intro a0 a1 a2 a3 a4 a5 a6 a7
    iintro %Φ HP HΦ
    ihave ⟨-, -, -, -, HH⟩ := H
    iapply HH $$ HP HΦ

end proof

end smd
end EtcdGrove
end Perennial
