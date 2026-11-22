/-
The proof of `ConditionsMap.Evaluate.spec`
(`Spec/k8s_io/apiserver/pkg/authorization/authorizer/ConditionsMap__Evaluate.lean`). Lean-first
(no Rocq counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsMap__Evaluate
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.partiallyEvaluateConditionsMapInternal
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionEvaluationResultError
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionEvaluationResultBoolean
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__UnconditionalPartsOrError
public import Proof.k8s_io.apiserver.pkg.authorization.authorizer.B2Lemmas

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

theorem ConditionsMap.Evaluate.wp_proof
    (wp_partiallyEvaluateConditionsMapInternal : EtcdGrove.authorizer.partiallyEvaluateConditionsMapInternal.spec (GF := GF) (hG := hG))
    (wp_ConditionEvaluationResultError : EtcdGrove.authorizer.ConditionEvaluationResultError.spec (GF := GF) (hG := hG))
    (wp_ConditionEvaluationResultBoolean : EtcdGrove.authorizer.ConditionEvaluationResultBoolean.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecision_UnconditionalPartsOrError : EtcdGrove.authorizer.ConditionsAwareDecision.UnconditionalPartsOrError.spec (GF := GF) (hG := hG)) :
    ConditionsMap.Evaluate.spec (GF := GF) (hG := hG) := by
  intro c dn no al ctx data f
  wp_start as ⟨#Hc, #Hf⟩
  wp_auto
  ipersist evaluateConditionFn
  wp_apply (wp_partiallyEvaluateConditionsMapInternal ctx c dn no al data) as %d #Hd
  · iframe #
    unfold maybeEvalFnOk
    iright
    iintro %ctx' %cond %data'
    unfold maybeEvalCallOk
    iintro !> %Ψ #Hcond HΨ
    rw [go.intoVal_unfold GoFunc]
    wp_auto
    ihave #Hf1 := evalFnOk_elim_b2 f ctx' cond data' $$ Hf
    ihave #Hcall := evalCallOk_elim_b2 f ctx' cond data' $$ Hf1
    wp_apply Hcall as %b %e #He
    · iexact Hcond
    rcases e with ei | _
    · wp_auto
      wp_apply wp_ConditionEvaluationResultError $$ [] as %e' #He'
      · iexact He
      (try wp_auto)
      iapply HΨ
      unfold resOk
      isplitr
      · ipureintro; word
      · iexact He'
    · wp_auto
      wp_apply wp_ConditionEvaluationResultBoolean
      (try wp_auto)
      iapply HΨ
      unfold resOk
      isplitr
      · ipureintro; split <;> word
      · iapply utilerrors.errTreeOrNil_nil
  unfold isWFDecisionLe
  icases Hd with ⟨%m, #Hdm, -⟩
  wp_apply (wp_ConditionsAwareDecision_UnconditionalPartsOrError d m) as %dec %r %e -
  · iframe #
  (try wp_auto)
  iapply HΦ
  itrivial

end proof

end authorizer
end EtcdGrove
end Perennial
