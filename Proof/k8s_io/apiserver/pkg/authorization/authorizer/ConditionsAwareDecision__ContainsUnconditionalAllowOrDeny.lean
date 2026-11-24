/-
The proof of `ConditionsAwareDecision.ContainsUnconditionalAllowOrDeny.spec` (`Spec/k8s_io/apiserv
er/pkg/authorization/authorizer/ConditionsAwareDecision__ContainsUnconditionalAllowOrDeny.lean`).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__ContainsUnconditionalAllowOrDeny
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__IsAllow
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__IsDeny
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__IsNoOpinion
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__IsConditionsMap
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecisionUnion__ContainsUnconditionalAllowOrDeny
public import Proof.k8s_io.apiserver.pkg.authorization.authorizer.PtrMethods
public import Proof.k8s_io.apiserver.pkg.authorization.authorizer.PtrMethodsB1

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace authorizer

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode k8s_io.apiserver.pkg.authorization.authorizer

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.authorization.authorizer.Assumptions]

theorem ConditionsAwareDecision.ContainsUnconditionalAllowOrDeny.wp_proof
    (wp_ConditionsAwareDecision_IsAllow : EtcdGrove.authorizer.ConditionsAwareDecision.IsAllow.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecision_IsDeny : EtcdGrove.authorizer.ConditionsAwareDecision.IsDeny.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecision_IsNoOpinion : EtcdGrove.authorizer.ConditionsAwareDecision.IsNoOpinion.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecision_IsConditionsMap : EtcdGrove.authorizer.ConditionsAwareDecision.IsConditionsMap.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecisionUnion_ContainsUnconditionalAllowOrDeny : EtcdGrove.authorizer.ConditionsAwareDecisionUnion.ContainsUnconditionalAllowOrDeny.spec (GF := GF) (hG := hG)) :
    ConditionsAwareDecision.ContainsUnconditionalAllowOrDeny.spec (GF := GF) (hG := hG) := by
  intro d m
  wp_start as #Hd
  icases isDecision_tag d m $$ Hd with %Htag
  wp_auto
  wp_apply (ConditionsAwareDecision.wp_ptr_IsAllow_of wp_ConditionsAwareDecision_IsAllow d_ptr
    (DFrac.own 1) d) $$ [$d] as Hdp
  rw [Htag]
  cases m with
  | allow =>
    simp only [Dec.cuad, Dec.tag] at Htag ⊢
    wp_auto
    iapply HΦ; itrivial
  | deny =>
    simp only [Dec.cuad, Dec.tag] at Htag ⊢
    wp_auto
    wp_apply (ConditionsAwareDecision.wp_ptr_IsDeny_of wp_ConditionsAwareDecision_IsDeny d_ptr
      (DFrac.own 1) d) $$ [$Hdp] as Hdp
    rw [Htag]
    try wp_auto
    iapply HΦ; itrivial
  | noOpinion =>
    simp only [Dec.cuad, Dec.tag] at Htag ⊢
    wp_auto
    wp_apply (ConditionsAwareDecision.wp_ptr_IsDeny_of wp_ConditionsAwareDecision_IsDeny d_ptr
      (DFrac.own 1) d) $$ [$Hdp] as Hdp
    rw [Htag]
    try wp_auto
    wp_apply (ConditionsAwareDecision.wp_ptr_IsNoOpinion_of wp_ConditionsAwareDecision_IsNoOpinion d_ptr
      (DFrac.own 1) d) $$ [$Hdp] as Hdp
    rw [Htag]
    try wp_auto
    iapply HΦ; itrivial
  | cmap dn no al =>
    simp only [Dec.cuad, Dec.tag] at Htag ⊢
    wp_auto
    wp_apply (ConditionsAwareDecision.wp_ptr_IsDeny_of wp_ConditionsAwareDecision_IsDeny d_ptr
      (DFrac.own 1) d) $$ [$Hdp] as Hdp
    rw [Htag]
    try wp_auto
    wp_apply (ConditionsAwareDecision.wp_ptr_IsNoOpinion_of wp_ConditionsAwareDecision_IsNoOpinion d_ptr
      (DFrac.own 1) d) $$ [$Hdp] as Hdp
    rw [Htag]
    try wp_auto
    wp_apply (ConditionsAwareDecision.wp_ptr_IsConditionsMap_of wp_ConditionsAwareDecision_IsConditionsMap
      d_ptr (DFrac.own 1) d) $$ [$Hdp] as Hdp
    rw [Htag]
    try wp_auto
    iapply HΦ; itrivial
  | union ks =>
    simp only [Dec.cuad, Dec.tag] at Htag ⊢
    wp_auto
    wp_apply (ConditionsAwareDecision.wp_ptr_IsDeny_of wp_ConditionsAwareDecision_IsDeny d_ptr
      (DFrac.own 1) d) $$ [$Hdp] as Hdp
    rw [Htag]
    try wp_auto
    wp_apply (ConditionsAwareDecision.wp_ptr_IsNoOpinion_of wp_ConditionsAwareDecision_IsNoOpinion d_ptr
      (DFrac.own 1) d) $$ [$Hdp] as Hdp
    rw [Htag]
    try wp_auto
    wp_apply (ConditionsAwareDecision.wp_ptr_IsConditionsMap_of wp_ConditionsAwareDecision_IsConditionsMap
      d_ptr (DFrac.own 1) d) $$ [$Hdp] as Hdp
    rw [Htag]
    try wp_auto
    icases (ConditionsAwareDecision.access_load'ConditionsAwareDecision'union d_ptr d
      (DFrac.own 1)).access_strict $$ Hdp with ⟨Hu, Hclose⟩
    ihave #Hsub := isDecision_union_subOk d ks $$ Hd
    unfold subOk
    icases Hsub with ⟨%Hc, -⟩
    wp_apply (wp_ConditionsAwareDecisionUnion_ContainsUnconditionalAllowOrDeny _ (DFrac.own 1) d.union')
      $$ [$Hu] as Hu
    rw [Hc]
    iapply HΦ; itrivial

end proof

end authorizer
end EtcdGrove
end Perennial
