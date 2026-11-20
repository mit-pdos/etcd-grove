/-
The proof of `ConditionsAwareDecision.IsUnconditional.spec` (`Spec/k8s_io/apiserver/pkg/authorizat
ion/authorizer/ConditionsAwareDecision__IsUnconditional.lean`). Lean-first (no Rocq counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__IsUnconditional
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__IsAllow
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__IsDeny
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__IsNoOpinion
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

theorem ConditionsAwareDecision.IsUnconditional.wp_proof
    (wp_ConditionsAwareDecision_IsAllow : EtcdGrove.authorizer.ConditionsAwareDecision.IsAllow.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecision_IsDeny : EtcdGrove.authorizer.ConditionsAwareDecision.IsDeny.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecision_IsNoOpinion : EtcdGrove.authorizer.ConditionsAwareDecision.IsNoOpinion.spec (GF := GF) (hG := hG)) :
    ConditionsAwareDecision.IsUnconditional.spec (GF := GF) (hG := hG) := by
  intro d
  wp_start
  wp_auto
  wp_apply (ConditionsAwareDecision.wp_ptr_IsAllow_of wp_ConditionsAwareDecision_IsAllow
    d_ptr (DFrac.own 1) d) $$ [$d] as Hd
  rw [Bool.decide_or, Bool.decide_or]
  cases h11 : decide (d.decisionType' = W64 11)
  · simp only [Bool.false_or]
    wp_auto
    wp_apply (ConditionsAwareDecision.wp_ptr_IsDeny_of wp_ConditionsAwareDecision_IsDeny
      d_ptr (DFrac.own 1) d) $$ [$Hd] as Hd
    cases h0 : decide (d.decisionType' = W64 0)
    · simp only [Bool.false_or]
      wp_auto
      wp_apply (ConditionsAwareDecision.wp_ptr_IsNoOpinion_of wp_ConditionsAwareDecision_IsNoOpinion
        d_ptr (DFrac.own 1) d) $$ [$Hd] as Hd
      iapply HΦ
      itrivial
    · simp only [Bool.true_or]
      wp_auto
      iapply HΦ
      itrivial
  · simp only [Bool.true_or]
    wp_auto
    iapply HΦ
    itrivial

end proof

end authorizer
end EtcdGrove
end Perennial
