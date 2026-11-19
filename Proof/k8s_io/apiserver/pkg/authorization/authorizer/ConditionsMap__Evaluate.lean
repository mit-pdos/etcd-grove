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
  sorry

end proof

end authorizer
end EtcdGrove
end Perennial
