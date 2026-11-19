/-
The proof of `ConditionsAwareDecision.FailureDecision.spec` (`Spec/k8s_io/apiserver/pkg/authorizat
ion/authorizer/ConditionsAwareDecision__FailureDecision.lean`). Lean-first (no Rocq counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__FailureDecision
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__PossibleDecisions
public import Spec.k8s_io.apimachinery.pkg.util.sets.Set__Has
public import Proof.k8s_io.apiserver.pkg.authorization.authorizer.PtrMethods

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

theorem ConditionsAwareDecision.FailureDecision.wp_proof
    (wp_ConditionsAwareDecision_PossibleDecisions : EtcdGrove.authorizer.ConditionsAwareDecision.PossibleDecisions.spec (GF := GF) (hG := hG))
    (wp_Set__Has : EtcdGrove.sets.Set.Has.spec (GF := GF) (hG := hG)) :
    ConditionsAwareDecision.FailureDecision.spec (GF := GF) (hG := hG) := by
  intro d m
  wp_start as #Hd
  simp only [DecisionDeny, DecisionNoOpinion]
  wp_auto
  wp_apply (ConditionsAwareDecision.wp_ptr_PossibleDecisions_of wp_ConditionsAwareDecision_PossibleDecisions
    d_ptr (DFrac.own 1) d m) $$ [$d] as %s ⟨⟨%S, HS, %HSm⟩, Hdp⟩
  · iexact Hd
  wp_apply (wp_Set__Has (K := w64) (T := Decision.ty) s (DFrac.own 1) S (W64 0)) $$ [$HS] as HS
  have hd : (S !! W64 0).isSome = m.pd.deny := by
    rw [HSm]; simp [PD.has]
  rw [hd]
  simp only [PD.failure]
  rcases Bool.eq_false_or_eq_true m.pd.deny with h | h <;>
    simp only [h, ite_true, Bool.false_eq_true, ite_false, decide_true, decide_false]
  · wp_auto
    iapply HΦ
    itrivial
  · wp_auto
    iapply HΦ
    itrivial

end proof

end authorizer
end EtcdGrove
end Perennial
