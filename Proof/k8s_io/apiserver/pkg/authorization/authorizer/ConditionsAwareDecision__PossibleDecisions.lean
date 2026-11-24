/-
The proof of `ConditionsAwareDecision.PossibleDecisions.spec` (`Spec/k8s_io/apiserver/pkg/authoriz
ation/authorizer/ConditionsAwareDecision__PossibleDecisions.lean`). Lean-first (no Rocq
counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__PossibleDecisions
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__IsAllow
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__IsNoOpinion
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__IsConditionsMap
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__IsUnion
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__ConditionsMap
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsMap__PossibleDecisions
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecisionUnion__PossibleDecisions
public import Spec.k8s_io.apimachinery.pkg.util.sets.New
public import Proof.k8s_io.apiserver.pkg.authorization.authorizer.PtrMethods
public import Proof.k8s_io.apiserver.pkg.authorization.authorizer.PtrMethodsB1
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

theorem ConditionsAwareDecision.PossibleDecisions.wp_proof
    (wp_ConditionsAwareDecision_IsAllow : EtcdGrove.authorizer.ConditionsAwareDecision.IsAllow.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecision_IsNoOpinion : EtcdGrove.authorizer.ConditionsAwareDecision.IsNoOpinion.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecision_IsConditionsMap : EtcdGrove.authorizer.ConditionsAwareDecision.IsConditionsMap.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecision_IsUnion : EtcdGrove.authorizer.ConditionsAwareDecision.IsUnion.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecision_ConditionsMap : EtcdGrove.authorizer.ConditionsAwareDecision.ConditionsMap.spec (GF := GF) (hG := hG))
    (wp_ConditionsMap_PossibleDecisions : EtcdGrove.authorizer.ConditionsMap.PossibleDecisions.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecisionUnion_PossibleDecisions : EtcdGrove.authorizer.ConditionsAwareDecisionUnion.PossibleDecisions.spec (GF := GF) (hG := hG))
    (wp_sets_New : EtcdGrove.sets.New.spec (GF := GF) (hG := hG)) :
    ConditionsAwareDecision.PossibleDecisions.spec (GF := GF) (hG := hG) := by
  intro d m
  wp_start as #Hd
  icases isDecision_tag d m $$ Hd with %Htag
  simp only [DecisionAllow, DecisionNoOpinion, DecisionDeny]
  wp_auto
  wp_apply (ConditionsAwareDecision.wp_ptr_IsAllow_of wp_ConditionsAwareDecision_IsAllow d_ptr
    (DFrac.own 1) d) $$ [$d] as Hdp
  rw [Htag]
  cases m with
  | allow =>
    wp_auto
    wp_apply wp_slice_literal (V := w64) [W64 1]
    isplitr
    · ipureintro; rfl
    iintro %nsl ⟨Hnsl, -⟩
    try wp_auto
    wp_apply (wp_sets_New (K := w64) (T := Decision.ty) _ _ [W64 1]) $$ [Hnsl] as %ns ⟨Hns, -⟩
    · iexact Hnsl
    try wp_auto
    iapply HΦ
    iexists _; iframe Hns; ipureintro
    exact setIs_congr (setIs_new [W64 1] (by simp)) (by simp [PD.ofList, Dec.pd])
  | deny =>
    wp_auto
    wp_apply (ConditionsAwareDecision.wp_ptr_IsNoOpinion_of wp_ConditionsAwareDecision_IsNoOpinion d_ptr
      (DFrac.own 1) d) $$ [$Hdp] as Hdp
    rw [Htag]
    try wp_auto
    wp_apply (ConditionsAwareDecision.wp_ptr_IsConditionsMap_of wp_ConditionsAwareDecision_IsConditionsMap d_ptr
      (DFrac.own 1) d) $$ [$Hdp] as Hdp
    rw [Htag]
    try wp_auto
    wp_apply (ConditionsAwareDecision.wp_ptr_IsUnion_of wp_ConditionsAwareDecision_IsUnion d_ptr
      (DFrac.own 1) d) $$ [$Hdp] as Hdp
    rw [Htag]
    try wp_auto
    wp_apply wp_slice_literal (V := w64) [W64 0]
    isplitr
    · ipureintro; rfl
    iintro %nsl ⟨Hnsl, -⟩
    try wp_auto
    wp_apply (wp_sets_New (K := w64) (T := Decision.ty) _ _ [W64 0]) $$ [Hnsl] as %ns ⟨Hns, -⟩
    · iexact Hnsl
    try wp_auto
    iapply HΦ
    iexists _; iframe Hns; ipureintro
    exact setIs_congr (setIs_new [W64 0] (by simp)) (by simp [PD.ofList, Dec.pd])
  | noOpinion =>
    wp_auto
    wp_apply (ConditionsAwareDecision.wp_ptr_IsNoOpinion_of wp_ConditionsAwareDecision_IsNoOpinion d_ptr
      (DFrac.own 1) d) $$ [$Hdp] as Hdp
    rw [Htag]
    try wp_auto
    wp_apply wp_slice_literal (V := w64) [W64 2]
    isplitr
    · ipureintro; rfl
    iintro %nsl ⟨Hnsl, -⟩
    try wp_auto
    wp_apply (wp_sets_New (K := w64) (T := Decision.ty) _ _ [W64 2]) $$ [Hnsl] as %ns ⟨Hns, -⟩
    · iexact Hnsl
    try wp_auto
    iapply HΦ
    iexists _; iframe Hns; ipureintro
    exact setIs_congr (setIs_new [W64 2] (by simp)) (by simp [PD.ofList, Dec.pd])
  | cmap dn no al =>
    simp only [Dec.tag] at Htag ⊢
    wp_auto
    wp_apply (ConditionsAwareDecision.wp_ptr_IsNoOpinion_of wp_ConditionsAwareDecision_IsNoOpinion d_ptr
      (DFrac.own 1) d) $$ [$Hdp] as Hdp
    rw [Htag]
    try wp_auto
    wp_apply (ConditionsAwareDecision.wp_ptr_IsConditionsMap_of wp_ConditionsAwareDecision_IsConditionsMap d_ptr
      (DFrac.own 1) d) $$ [$Hdp] as Hdp
    rw [Htag]
    try wp_auto
    wp_apply (ConditionsAwareDecision.wp_ptr_ConditionsMap_of wp_ConditionsAwareDecision_ConditionsMap
      d_ptr (DFrac.own 1) d) $$ [$Hdp] as Hdp
    icases isDecision_cmap_slices d dn no al $$ Hd with ⟨#Hdn, #Hal⟩
    wp_apply (wp_ConditionsMap_PossibleDecisions d.conditionsMap' DFrac.discard DFrac.discard dn al)
      $$ [$Hdn $Hal] as %s ⟨⟨%S, HS, %HSm⟩, -⟩
    iapply HΦ
    iexists _; iframe HS; ipureintro
    exact HSm
  | union ks =>
    simp only [Dec.tag] at Htag ⊢
    wp_auto
    wp_apply (ConditionsAwareDecision.wp_ptr_IsNoOpinion_of wp_ConditionsAwareDecision_IsNoOpinion d_ptr
      (DFrac.own 1) d) $$ [$Hdp] as Hdp
    rw [Htag]
    try wp_auto
    wp_apply (ConditionsAwareDecision.wp_ptr_IsConditionsMap_of wp_ConditionsAwareDecision_IsConditionsMap d_ptr
      (DFrac.own 1) d) $$ [$Hdp] as Hdp
    rw [Htag]
    try wp_auto
    wp_apply (ConditionsAwareDecision.wp_ptr_IsUnion_of wp_ConditionsAwareDecision_IsUnion d_ptr
      (DFrac.own 1) d) $$ [$Hdp] as Hdp
    rw [Htag]
    try wp_auto
    icases (ConditionsAwareDecision.access_load'ConditionsAwareDecision'union d_ptr d
      (DFrac.own 1)).access_strict $$ Hdp with ⟨Hu, Hclose⟩
    ihave #Hsub := isDecision_union_subOk d ks $$ Hd
    wp_apply (wp_ConditionsAwareDecisionUnion_PossibleDecisions _ (DFrac.own 1) d.union' DFrac.discard ks)
      $$ [$Hu $Hsub] as %s ⟨⟨%S, HS, %HSm⟩, Hu, -⟩
    iapply HΦ
    iexists _; iframe HS; ipureintro
    exact HSm


end proof

end authorizer
end EtcdGrove
end Perennial
