/-
The proof of `PartiallyEvaluateConditionsAwareDecision.spec` (`Spec/k8s_io/apiserver/pkg/authoriza
tion/authorizer/PartiallyEvaluateConditionsAwareDecision.lean`). Lean-first (no Rocq counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.PartiallyEvaluateConditionsAwareDecision
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__IsConditionsMap
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__ConditionsMap
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.partiallyEvaluateConditionsMapInternal
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__IsUnion
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__UnionedDecisions
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecisionUnion__Add
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__ContainsUnconditionalAllowOrDeny
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecisionUnion__ToDecision
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__IsUnconditional

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

theorem PartiallyEvaluateConditionsAwareDecision.wp_proof
    (wp_ConditionsAwareDecision_IsConditionsMap : EtcdGrove.authorizer.ConditionsAwareDecision.IsConditionsMap.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecision_ConditionsMap : EtcdGrove.authorizer.ConditionsAwareDecision.ConditionsMap.spec (GF := GF) (hG := hG))
    (wp_partiallyEvaluateConditionsMapInternal : EtcdGrove.authorizer.partiallyEvaluateConditionsMapInternal.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecision_IsUnion : EtcdGrove.authorizer.ConditionsAwareDecision.IsUnion.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecision_UnionedDecisions : EtcdGrove.authorizer.ConditionsAwareDecision.UnionedDecisions.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecisionUnion_Add : EtcdGrove.authorizer.ConditionsAwareDecisionUnion.Add.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecision_ContainsUnconditionalAllowOrDeny : EtcdGrove.authorizer.ConditionsAwareDecision.ContainsUnconditionalAllowOrDeny.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecisionUnion_ToDecision : EtcdGrove.authorizer.ConditionsAwareDecisionUnion.ToDecision.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecision_IsUnconditional : EtcdGrove.authorizer.ConditionsAwareDecision.IsUnconditional.spec (GF := GF) (hG := hG)) :
    PartiallyEvaluateConditionsAwareDecision.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end authorizer
end EtcdGrove
end Perennial
