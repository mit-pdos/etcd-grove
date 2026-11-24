/-
The proof of `twoPhase.spec`
(`Spec/github_com/mit_pdos/etcd_grove/examples/k8s/authz/twoPhase.lean`). Lean-first (no Rocq
counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.authz.twoPhase
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__PossibleDecisions
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__IsAllow
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__FailureDecision
public import Spec.k8s_io.apimachinery.pkg.util.sets.Set__Has
public import Spec.k8s_io.apiserver.pkg.authorization.union.unionAuthzHandler__EvaluateConditions
public import Proof.k8s_io.apiserver.pkg.authorization.authorizer.PtrMethods
public import Proof.k8s_io.apimachinery.pkg.util.sets.PtrMethods

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_authz

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode k8s_io.apiserver.pkg.authorization.authorizer k8s_io.apiserver.pkg.authorization.union github_com.mit_pdos.etcd_grove.examples.k8s.authz EtcdGrove.authorizer EtcdGrove.union

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.authz.Assumptions]

theorem twoPhase.wp_proof
    (wp_ConditionsAwareDecision_PossibleDecisions : EtcdGrove.authorizer.ConditionsAwareDecision.PossibleDecisions.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecision_IsAllow : EtcdGrove.authorizer.ConditionsAwareDecision.IsAllow.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecision_FailureDecision : EtcdGrove.authorizer.ConditionsAwareDecision.FailureDecision.spec (GF := GF) (hG := hG))
    (wp_Set__Has : EtcdGrove.sets.Set.Has.spec (GF := GF) (hG := hG))
    (wp_unionAuthzHandler_EvaluateConditions : EtcdGrove.union.unionAuthzHandler.EvaluateConditions.spec (GF := GF) (hG := hG)) :
    twoPhase.spec (GF := GF) (hG := hG) := by
  intro ctx h d m
  wp_start as ⟨#Hu, #Hd, %Hwf', #Hdn⟩
  have Hwf := Hwf'.1
  have Hfit : Dec.foldFits authzNameMax m :=
    Dec.foldFits_of_le _ m _ _ Hwf'.2.2 Hwf'.2.1 authz_foldBound_lt
  icases isDecision_tag d m $$ Hd with %Htag
  wp_auto
  wp_apply (ConditionsAwareDecision.wp_ptr_PossibleDecisions_of
    wp_ConditionsAwareDecision_PossibleDecisions d_ptr (DFrac.own 1) d m) $$ [$d]
    as %s ⟨⟨%S, HS, %HSm⟩, Hdp⟩
  · iexact Hd
  (try wp_auto)
  wp_apply (ConditionsAwareDecision.wp_ptr_IsAllow_of wp_ConditionsAwareDecision_IsAllow
    d_ptr (DFrac.own 1) d) $$ [$Hdp] as Hdp
  rw [Htag, Dec.tag_allow]
  cases hA : m.isAllow
  · wp_auto
    wp_apply (ConditionsAwareDecision.wp_ptr_FailureDecision_of
      wp_ConditionsAwareDecision_FailureDecision d_ptr (DFrac.own 1) d m) $$ [$Hdp] as Hdp
    · iexact Hd
    (try wp_auto)
    wp_apply (sets.Set.wp_ptr_Has_of wp_Set__Has pd_ptr (DFrac.own 1) s (DFrac.own 1) S
      m.pd.failure) $$ [$pd $HS] as ⟨pd, HS⟩
    rw [HSm, Dec.failure_mem m Hwf hA]
    wp_auto
    wp_apply (sets.Set.wp_ptr_Has_of wp_Set__Has pd_ptr (DFrac.own 1) s (DFrac.own 1) S
      (W64 1)) $$ [$pd $HS] as ⟨pd, HS⟩
    rw [HSm]
    cases hAl : m.pd.has (W64 1)
    · wp_auto
      iapply HΦ
      itrivial
    · wp_auto
      wp_apply (wp_unionAuthzHandler_EvaluateConditions h ctx d m _) as %dec %r %e %Hdec
      · iframe #
        ipureintro; exact ⟨Hwf, Hfit⟩
      -- C2: the decision is possible (its failure decision is, by C3)
      have Hpd : m.pd.has dec = true := by
        rcases Hdec with Hdec | Hdec
        · exact Hdec
        · rw [Hdec]; exact Dec.failure_mem m Hwf hA
      -- C1: so it is Deny, Allow or NoOpinion
      have H3 := PD.has_valid m.pd dec Hpd
      rcases H3 with rfl | rfl | rfl
      all_goals
        wp_auto
        wp_apply (sets.Set.wp_ptr_Has_of wp_Set__Has pd_ptr (DFrac.own 1) s (DFrac.own 1) S _)
          $$ [$pd $HS] as ⟨pd, HS⟩
        rw [HSm, Hpd]
        wp_auto
        iapply HΦ
        itrivial
  · wp_auto
    iapply HΦ
    itrivial

end proof

end k8s_authz
end EtcdGrove
end Perennial
