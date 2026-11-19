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
  sorry

end proof

end authorizer
end EtcdGrove
end Perennial
