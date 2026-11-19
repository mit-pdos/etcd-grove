/-
`schema.TypeRef.Equals`: a member of the recursion cluster `schema.EqualsRec` (`EqualsRec.lean`); its proof is the
projection of the cluster's (its body is `TypeRef__EqualsBody.lean`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.schema.TypeRef__EqualsBody
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

theorem schema.TypeRef.Equals.wp_proofBody :
    schema.TypeRef.Equals.specBody (GF := GF) := by
  unfold schema.TypeRef.Equals.specBody schema.EqualsRec.specI schema.Atom.Equals.specI
    schema.List.Equals.specI schema.Map.Equals.specI schema.StructField.Equals.specI
    schema.TypeRef.Equals.specI
  iintro #IH
  iintro %a %b %dq1 %dq2 %ta %tb %oa %ob
  wp_start as ⟨Ha, #Hta, Hb, #Htb⟩
  ihave %Hane := typedPointsto_not_null $$ Ha
  ihave %Hbne := typedPointsto_not_null $$ Hb
  iStructNamedSuffix Ha "a"
  iStructNamedSuffix Hb "b"
  wp_auto
  wp_if_destruct
  all_goals try (exfalso; exact Hane rfl)
  wp_if_destruct
  all_goals try (exfalso; exact Hbne rfl)
  ihave %Hera := LawProofs.isTypeRefOpt_er ta oa $$ Hta
  ihave %Herb := LawProofs.isTypeRefOpt_er tb ob $$ Htb
  cases oa with
  | none =>
    ihave %Hza := (isTypeRefOpt_none_law_holds ta).1 $$ Hta
    subst Hza
    cases ob with
    | none =>
      ihave %Hzb := (isTypeRefOpt_none_law_holds tb).1 $$ Htb
      subst Hzb
      wp_auto
      ihave ⟨#HA, -⟩ := IH
      ihave #Hz : isAtomOpt (GF := GF) (zero_val schema.TypeRef).Inlined' none $$ []
      · iapply (isAtomOpt_none_law_holds _).2; ipureintro; rfl
      wp_apply HA $$ [Inlineda Inlinedb] as %r ⟨Inlineda, Inlinedb, %hr⟩
      · iframe; iframe #
      iapply HΦ
      isplitl [NamedTypea Inlineda ElementRelationshipa Nullablea]
      · iapply typedPointsto_combine _ _ _ Hane
        simp only [TypedPointsto.typedPointstoDef]
        iframe
      isplitl [NamedTypeb Inlinedb ElementRelationshipb Nullableb]
      · iapply typedPointsto_combine _ _ _ Hbne
        simp only [TypedPointsto.typedPointstoDef]
        iframe
      ipureintro; simpa using hr
    | some t' =>
      ihave Htb' := (isTypeRefOpt_some_law_holds tb t').1 $$ Htb
      ihave ⟨#Hnb, %Htzb⟩ := isTypeRef_elim_law_holds tb t' $$ Htb'
      ihave %Hnnb := typedPointsto_not_null $$ Hnb
      try simp only [Hnnb, decide_false]
      wp_auto
      iapply HΦ
      isplitl [NamedTypea Inlineda ElementRelationshipa Nullablea]
      · iapply typedPointsto_combine _ _ _ Hane
        simp only [TypedPointsto.typedPointstoDef]
        iframe
      isplitl [NamedTypeb Inlinedb ElementRelationshipb Nullableb]
      · iapply typedPointsto_combine _ _ _ Hbne
        simp only [TypedPointsto.typedPointstoDef]
        iframe
      ipureintro; simp
  | some t =>
    ihave Hta' := (isTypeRefOpt_some_law_holds ta t).1 $$ Hta
    ihave ⟨#Hna, %Htza⟩ := isTypeRef_elim_law_holds ta t $$ Hta'
    ihave %Hnna := typedPointsto_not_null $$ Hna
    cases ob with
    | none =>
      ihave %Hzb := (isTypeRefOpt_none_law_holds tb).1 $$ Htb
      subst Hzb
      try simp only [Hnna, decide_false]
      wp_auto
      iapply HΦ
      isplitl [NamedTypea Inlineda ElementRelationshipa Nullablea]
      · iapply typedPointsto_combine _ _ _ Hane
        simp only [TypedPointsto.typedPointstoDef]
        iframe
      isplitl [NamedTypeb Inlinedb ElementRelationshipb Nullableb]
      · iapply typedPointsto_combine _ _ _ Hbne
        simp only [TypedPointsto.typedPointstoDef]
        iframe
      ipureintro; simp
    | some t' =>
      ihave Htb' := (isTypeRefOpt_some_law_holds tb t').1 $$ Htb
      ihave ⟨#Hnb, %Htzb⟩ := isTypeRef_elim_law_holds tb t' $$ Htb'
      ihave %Hnnb := typedPointsto_not_null $$ Hnb
      cases ta with | mk na ia ea ba =>
      cases tb with | mk nb ib eb bb =>
      simp only at Htza Htzb Hnna Hnnb
      obtain ⟨rfl, rfl, rfl⟩ := Htza
      obtain ⟨rfl, rfl, rfl⟩ := Htzb
      simp only [Hnna, Hnnb, decide_false]
      wp_auto
      wp_if_destruct
      · exact absurd rfl Hnna
      wp_if_destruct
      · have Hname := Hif
        wp_if_destruct
        · have Hnull := Hif
          ihave ⟨#HA, -⟩ := IH
          ihave #Hz : isAtomOpt (GF := GF) (zero_val schema.Atom) none $$ []
          · iapply (isAtomOpt_none_law_holds _).2; ipureintro; rfl
          wp_apply HA $$ [Inlineda Inlinedb] as %r ⟨Inlineda, Inlinedb, %hr⟩
          · iframe; iframe #
          iapply HΦ
          isplitl [NamedTypea Inlineda ElementRelationshipa Nullablea]
          · iapply typedPointsto_combine _ _ _ Hane
            simp only [TypedPointsto.typedPointstoDef]
            iframe
          isplitl [NamedTypeb Inlinedb ElementRelationshipb Nullableb]
          · iapply typedPointsto_combine _ _ _ Hbne
            simp only [TypedPointsto.typedPointstoDef]
            iframe
          ipureintro
          obtain ⟨tn, tb⟩ := t
          obtain ⟨tn', tb'⟩ := t'
          simp only at Hname Hnull
          subst Hname Hnull
          simpa using hr
        · have Hnull := Hif
          iapply HΦ
          isplitl [NamedTypea Inlineda ElementRelationshipa Nullablea]
          · iapply typedPointsto_combine _ _ _ Hane
            simp only [TypedPointsto.typedPointstoDef]
            iframe
          isplitl [NamedTypeb Inlinedb ElementRelationshipb Nullableb]
          · iapply typedPointsto_combine _ _ _ Hbne
            simp only [TypedPointsto.typedPointstoDef]
            iframe
          ipureintro
          simp only [Bool.false_eq_true, false_iff, Option.some.injEq]
          rintro rfl; exact Hnull rfl
      · have Hname := Hif
        iapply HΦ
        isplitl [NamedTypea Inlineda ElementRelationshipa Nullablea]
        · iapply typedPointsto_combine _ _ _ Hane
          simp only [TypedPointsto.typedPointstoDef]
          iframe
        isplitl [NamedTypeb Inlinedb ElementRelationshipb Nullableb]
        · iapply typedPointsto_combine _ _ _ Hbne
          simp only [TypedPointsto.typedPointstoDef]
          iframe
        ipureintro
        simp only [Bool.false_eq_true, false_iff, Option.some.injEq]
        rintro rfl; exact Hname rfl

end proof

end smd
end EtcdGrove
end Perennial
