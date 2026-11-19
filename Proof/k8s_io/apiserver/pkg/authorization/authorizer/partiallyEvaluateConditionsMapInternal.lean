/-
The proof of `partiallyEvaluateConditionsMapInternal.spec` (`Spec/k8s_io/apiserver/pkg/authorizati
on/authorizer/partiallyEvaluateConditionsMapInternal.lean`). Lean-first (no Rocq counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.partiallyEvaluateConditionsMapInternal
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionEvaluationResult__IsUnevaluatable
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecisionNoOpinion
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsMap__DenyConditions
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.conditionsToAppliedErroredUnevaluated
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecisionDeny
public import Spec.k8s_io.apimachinery.pkg.util.errors.NewAggregate
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecisionConditionsMap
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsMap__NoOpinionConditions
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsMap__AllowConditions
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecisionAllow

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

theorem partiallyEvaluateConditionsMapInternal.wp_proof
    (wp_ConditionEvaluationResult_IsUnevaluatable : EtcdGrove.authorizer.ConditionEvaluationResult.IsUnevaluatable.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecisionNoOpinion : EtcdGrove.authorizer.ConditionsAwareDecisionNoOpinion.spec (GF := GF) (hG := hG))
    (wp_ConditionsMap_DenyConditions : EtcdGrove.authorizer.ConditionsMap.DenyConditions.spec (GF := GF) (hG := hG))
    (wp_conditionsToAppliedErroredUnevaluated : EtcdGrove.authorizer.conditionsToAppliedErroredUnevaluated.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecisionDeny : EtcdGrove.authorizer.ConditionsAwareDecisionDeny.spec (GF := GF) (hG := hG))
    (wp_NewAggregate : EtcdGrove.utilerrors.NewAggregate.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecisionConditionsMap : EtcdGrove.authorizer.ConditionsAwareDecisionConditionsMap.spec (GF := GF) (hG := hG))
    (wp_ConditionsMap_NoOpinionConditions : EtcdGrove.authorizer.ConditionsMap.NoOpinionConditions.spec (GF := GF) (hG := hG))
    (wp_ConditionsMap_AllowConditions : EtcdGrove.authorizer.ConditionsMap.AllowConditions.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecisionAllow : EtcdGrove.authorizer.ConditionsAwareDecisionAllow.spec (GF := GF) (hG := hG)) :
    partiallyEvaluateConditionsMapInternal.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end authorizer
end EtcdGrove
end Perennial
