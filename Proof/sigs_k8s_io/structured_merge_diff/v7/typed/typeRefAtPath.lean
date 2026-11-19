/-
`typed.typeRefAtPath`: not proved yet (`sorry`): the stage's Prove step, after the freeze
(notes/smd-plan.md). Draft (2026-11-19).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.typeRefAtPath
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsBPers
public import Proof.sigs_k8s_io.structured_merge_diff.v7.schema.LawProofs
public import Spec.sigs_k8s_io.structured_merge_diff.v7.schema.Map__FindField

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
variable [package_sem : typed.Assumptions]

theorem typed.typeRefAtPath.wp_proof
    (h_Map_FindField : schema.Map.FindField.spec (GF := GF)) :
    typed.typeRefAtPath.spec (GF := GF) := fun mp fs e rel pe pe' => by
  wp_start as ⟨#Hm, #Hpe, %Hnd⟩
  icases isMapRep_elim_law_holds mp fs e rel $$ Hm with
    ⟨%fsl, %sfs, %etv, -, -, -, -, -, #Het, #Hetv, -⟩
  ihave Hfn := isPE_fieldName pe pe' $$ Hpe
  -- the element type's answer: `tr != TypeRef{}` iff the type is present
  have hcmp : ∀ (o : Option TypeRef) (tr : schema.TypeRef), isTypeRefOpt (GF := GF) tr o ⊢
      ⌜(tr = zero_val schema.TypeRef ↔ o = none)⌝ := by
    intro o tr
    rcases o with _ | t
    · iintro H; ihave %h := (isTypeRefOpt_none_law_holds tr).1 $$ H; ipureintro; simp [h]
    · iintro H; ihave H := (isTypeRefOpt_some_law_holds tr t).1 $$ H
      icases isTypeRef_elim_law_holds tr t $$ H with ⟨Hn, -⟩
      ihave %h := typedPointsto_not_null _ _ _ $$ Hn
      ipureintro; simp only [reduceCtorEq, iff_false]
      intro htr; rw [htr] at h; exact h rfl
  ihave %Hetz := hcmp e etv $$ Hetv
  wp_auto
  trace_state
  sorry

end proof

end smd
end EtcdGrove
end Perennial
