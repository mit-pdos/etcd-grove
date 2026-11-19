/-
The proof of `ConditionsAwareDecisionUnion.FailureDecision.spec` (`Spec/k8s_io/apiserver/pkg/autho
rization/authorizer/ConditionsAwareDecisionUnion__FailureDecision.lean`). Lean-first (no Rocq
counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecisionUnion__FailureDecision
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecisionUnion__PossibleDecisions
public import Spec.k8s_io.apimachinery.pkg.util.sets.Set__Has

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

theorem ConditionsAwareDecisionUnion.FailureDecision.wp_proof
    (wp_ConditionsAwareDecisionUnion_PossibleDecisions : EtcdGrove.authorizer.ConditionsAwareDecisionUnion.PossibleDecisions.spec (GF := GF) (hG := hG))
    (wp_Set__Has : EtcdGrove.sets.Set.Has.spec (GF := GF) (hG := hG)) :
    ConditionsAwareDecisionUnion.FailureDecision.spec (GF := GF) (hG := hG) := by
  intro p dq u dq' ks
  wp_start as ⟨Hp, Hsub⟩
  wp_auto
  wp_apply (wp_ConditionsAwareDecisionUnion_PossibleDecisions p dq u dq' ks) $$ [$Hp $Hsub]
    as %s ⟨⟨%S, HS, %HSm⟩, Hp, Hsub⟩
  simp only [DecisionDeny, DecisionNoOpinion]
  wp_apply (wp_Set__Has (K := w64) (T := Decision.ty) s (DFrac.own 1) S (W64 0)) $$ [$HS] as HS
  have hd : (S !! W64 0).isSome = (Dec.subL ks).deny := by
    rw [HSm]; simp [PD.has, Dec.pd]
  rw [hd]
  simp only [PD.failure, Dec.pd]
  rcases Bool.eq_false_or_eq_true (Dec.subL ks).deny with h | h <;> simp only [h, ite_true, Bool.false_eq_true, ite_false, decide_true, decide_false]
  · wp_auto
    iapply HΦ
    iframe
  · wp_auto
    iapply HΦ
    iframe

end proof

end authorizer
end EtcdGrove
end Perennial
