/-
The proof of `ConditionsAwareDecisionConditionsMap.spec`
(`Spec/k8s_io/apiserver/pkg/authorization/authorizer/ConditionsAwareDecisionConditionsMap.lean`).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecisionConditionsMap
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecisionDeny
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecisionNoOpinion
public import Spec.fmt.ErrorfAny
public import Spec.k8s_io.apimachinery.pkg.util.sets.New
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.validateConditions
public import Spec.slices.Clone

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

theorem ConditionsAwareDecisionConditionsMap.wp_proof
    (wp_ConditionsAwareDecisionDeny : EtcdGrove.authorizer.ConditionsAwareDecisionDeny.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecisionNoOpinion : EtcdGrove.authorizer.ConditionsAwareDecisionNoOpinion.spec (GF := GF) (hG := hG))
    (wp_ErrorfAny : EtcdGrove.fmt.ErrorfAny.spec (GF := GF) (hG := hG))
    (wp_sets_New : EtcdGrove.sets.New.spec (GF := GF) (hG := hG))
    (wp_validateConditions : EtcdGrove.authorizer.validateConditions.spec (GF := GF) (hG := hG))
    (wp_Clone : EtcdGrove.slices.Clone.spec (GF := GF) (hG := hG)) :
    ConditionsAwareDecisionConditionsMap.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end authorizer
end EtcdGrove
end Perennial
