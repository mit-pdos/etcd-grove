/-
`schema.StructField.Equals`: a member of the recursion cluster `schema.EqualsRec` (`EqualsRec.lean`); its proof is the
projection of the cluster's (its body is `StructField__EqualsBody.lean`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.schema.StructField__EqualsBody
public import Spec.reflect.DeepEqualNil
public import Proof.sigs_k8s_io.structured_merge_diff.v7.schema.LawProofs

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

theorem schema.StructField.Equals.wp_proofBody
    (h_reflect_DeepEqual_Nil : _root_.Perennial.EtcdGrove.reflect.DeepEqual.specNil (GF := GF) (hG := hG)) :
    schema.StructField.Equals.specBody (GF := GF) := by
  unfold schema.StructField.Equals.specBody schema.EqualsRec.specI schema.Atom.Equals.specI
    schema.List.Equals.specI schema.Map.Equals.specI schema.StructField.Equals.specI
    schema.TypeRef.Equals.specI
  iintro #IH
  iintro %a %b %dq1 %dq2 %sa %sb %f %g
  wp_start as ⟨Ha, #Hsa, Hb, #Hsb⟩
  ihave %Hane := typedPointsto_not_null $$ Ha
  ihave %Hbne := typedPointsto_not_null $$ Hb
  icases (isStructField_elim_law_holds sa f).1 $$ Hsa with ⟨%hfa, #Hta⟩
  icases (isStructField_elim_law_holds sb g).1 $$ Hsb with ⟨%hfb, #Htb⟩
  cases sa with | mk na ta da =>
  cases sb with | mk nb tb db =>
  simp only at hfa hfb
  obtain ⟨rfl, rfl⟩ := hfa
  obtain ⟨rfl, rfl⟩ := hfb
  iStructNamedSuffix Ha "a"
  iStructNamedSuffix Hb "b"
  wp_auto
  wp_if_destruct
  all_goals try (exfalso; exact Hane rfl)
  all_goals try wp_if_destruct
  all_goals try (exact (Hbne rfl).elim)
  wp_if_destruct
  · have Hname := Hif
    wp_apply h_reflect_DeepEqual_Nil
    ihave ⟨-, -, -, -, #HT⟩ := IH
    wp_apply HT $$ [Type'a Type'b] as %r ⟨Type'a, Type'b, %hr⟩
    · iframe
      isplitl
      · iapply (isTypeRefOpt_some_law_holds _ _).2; iexact Hta
      · iapply (isTypeRefOpt_some_law_holds _ _).2; iexact Htb
    iapply HΦ
    isplitl [Namea Type'a Defaulta]
    · iapply typedPointsto_combine _ _ _ Hane
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    isplitl [Nameb Type'b Defaultb]
    · iapply typedPointsto_combine _ _ _ Hbne
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    ipureintro
    obtain ⟨fn, ft⟩ := f
    obtain ⟨gn, gt⟩ := g
    simp only at Hname
    subst Hname
    simpa using hr
  iapply HΦ
  isplitl [Namea Type'a Defaulta]
  · iapply typedPointsto_combine _ _ _ Hane
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  isplitl [Nameb Type'b Defaultb]
  · iapply typedPointsto_combine _ _ _ Hbne
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  ipureintro
  simp only [Bool.false_eq_true, false_iff]
  rintro rfl; exact Hif rfl

end proof

end smd
end EtcdGrove
end Perennial
