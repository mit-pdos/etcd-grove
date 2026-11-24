/-
The proof of `ConditionsAwareDecisionUnion.PossibleDecisions.spec` (`Spec/k8s_io/apiserver/pkg/aut
horization/authorizer/ConditionsAwareDecisionUnion__PossibleDecisions.lean`). Lean-first (no Rocq
counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecisionUnion__PossibleDecisions
public import Spec.k8s_io.apimachinery.pkg.util.sets.New
public import Spec.k8s_io.apimachinery.pkg.util.sets.Set__UnsortedList
public import Spec.k8s_io.apimachinery.pkg.util.sets.Set__Insert
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecisionUnion__ContainsUnconditionalAllowOrDeny
public import Spec.k8s_io.apimachinery.pkg.util.sets.Set__Delete
public import Proof.k8s_io.apimachinery.pkg.util.sets.PtrMethods
public import Proof.k8s_io.apimachinery.pkg.util.sets.PtrMethodsB1
public import Proof.k8s_io.apiserver.pkg.authorization.authorizer.B1Lemmas

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace authorizer

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode k8s_io.apiserver.pkg.authorization.authorizer sets

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.authorization.authorizer.Assumptions]

theorem ConditionsAwareDecisionUnion.PossibleDecisions.wp_proof
    (wp_sets_New : EtcdGrove.sets.New.spec (GF := GF) (hG := hG))
    (wp_Set__UnsortedList : EtcdGrove.sets.Set.UnsortedList.spec (GF := GF) (hG := hG))
    (wp_Set__Insert : EtcdGrove.sets.Set.Insert.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecisionUnion_ContainsUnconditionalAllowOrDeny : EtcdGrove.authorizer.ConditionsAwareDecisionUnion.ContainsUnconditionalAllowOrDeny.spec (GF := GF) (hG := hG))
    (wp_Set__Delete : EtcdGrove.sets.Set.Delete.spec (GF := GF) (hG := hG)) :
    ConditionsAwareDecisionUnion.PossibleDecisions.spec (GF := GF) (hG := hG) := by
  intro p dq u dq' ks
  wp_start as ⟨Hp, Hsub⟩
  simp only [DecisionNoOpinion]
  wp_auto
  wp_apply wp_slice_literal (V := w64) [W64 2]
  isplitr
  · ipureintro; rfl
  iintro %nsl ⟨Hnsl, -⟩
  try wp_auto
  wp_apply (wp_sets_New (K := w64) (T := Decision.ty) _ _ [W64 2]) $$ [Hnsl] as %m ⟨Hm, -⟩
  · iexact Hnsl
  try wp_auto
  have Hs0 : setIs (insertAll ∅ [W64 2]) ⟨false, false, true⟩ :=
    setIs_congr (setIs_new [W64 2] (by simp)) (by simp [PD.ofList])
  icases (ConditionsAwareDecisionUnion.access_load'ConditionsAwareDecisionUnion'subDecisionsPossibleDecisions
    p u dq).access_strict $$ Hp with ⟨Hf, Hclose⟩
  unfold subOk
  icases Hsub with ⟨%Hc, Hsub⟩
  icases Hsub with (⟨%Hks, %Hnil⟩ | ⟨%S, HS, %HSm⟩)
  · subst Hks
    rw [Hnil]
    wp_auto
    ihave Hp := Hclose $$ Hf
    wp_apply (wp_ConditionsAwareDecisionUnion_ContainsUnconditionalAllowOrDeny p dq u) $$ [$Hp] as Hp
    rw [Hc]
    simp only [Dec.cuadL]
    wp_auto
    iapply HΦ
    iframe
    isplitr
    · ipureintro; exact setIs_congr Hs0 (by simp [Dec.pd, Dec.subL, Dec.cuadL, PD.empty])
    isplitr
    · itrivial
    ileft; ipureintro; exact ⟨trivial, trivial⟩
  · ihave %Hnn := ownMap_not_nil _ _ _ $$ HS
    wp_auto
    rw [decide_eq_false Hnn, Bool.not_false]
    wp_auto
    wp_apply (Set.wp_ptr_UnsortedList_of (T := Decision.ty) wp_Set__UnsortedList _ dq _ dq' S)
      $$ [$Hf $HS] as %sl %ks' ⟨Hf, HS, Hsl, %Hks'⟩
    wp_apply (Set.wp_ptr_Insert_of (T := Decision.ty) wp_Set__Insert possibleDecisions_ptr (DFrac.own 1) m _ _ _ ks')
      $$ [$possibleDecisions $Hm $Hsl] as ⟨possibleDecisions, Hm, -⟩
    have HS1 := setIs_insertAll_set _ S _ _ ks' Hs0 HSm Hks'.1
    ihave Hp := Hclose $$ Hf
    wp_apply (wp_ConditionsAwareDecisionUnion_ContainsUnconditionalAllowOrDeny p dq u) $$ [$Hp] as Hp
    rw [Hc]
    cases hcu : Dec.cuadL ks
    · wp_auto
      iapply HΦ
      iframe
      isplitr
      · ipureintro; exact setIs_congr HS1 (by simp [PD.or, Dec.pd, hcu])
      isplitr
      · itrivial
      iright; iexists S; iframe HS; ipureintro; exact HSm
    · wp_auto
      wp_apply wp_slice_literal (V := w64) [W64 2]
      isplitr
      · ipureintro; rfl
      iintro %dsl ⟨Hdsl, -⟩
      try wp_auto
      wp_apply (Set.wp_ptr_Delete_of (T := Decision.ty) wp_Set__Delete possibleDecisions_ptr (DFrac.own 1) m _ _ _
        [W64 2]) $$ [$possibleDecisions $Hm $Hdsl] as ⟨possibleDecisions, Hm, -⟩
      iapply HΦ
      iframe
      isplitr
      · ipureintro
        exact setIs_congr (setIs_deleteNoOpinion _ _ HS1) (by simp [PD.or, Dec.pd, hcu])
      isplitr
      · itrivial
      iright; iexists S; iframe HS; ipureintro; exact HSm

end proof

end authorizer
end EtcdGrove
end Perennial
