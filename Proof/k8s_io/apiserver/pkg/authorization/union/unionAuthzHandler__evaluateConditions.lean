/-
The proof of `unionAuthzHandler.evaluateConditions.spec`
(`Spec/k8s_io/apiserver/pkg/authorization/union/unionAuthzHandler__evaluateConditions.lean`).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.authorization.union.unionAuthzHandler__evaluateConditions
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__FailureDecision
public import Spec.fmt.ErrorfAny

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace union

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode k8s_io.apiserver.pkg.authorization.authorizer k8s_io.apiserver.pkg.authorization.union EtcdGrove.authorizer

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.authorization.union.Assumptions]

theorem unionAuthzHandler.evaluateConditions.wp_proof
    (wp_ConditionsAwareDecision_FailureDecision : EtcdGrove.authorizer.ConditionsAwareDecision.FailureDecision.spec (GF := GF) (hG := hG))
    (wp_ErrorfAny : EtcdGrove.fmt.ErrorfAny.spec (GF := GF) (hG := hG)) :
    unionAuthzHandler.evaluateConditions.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end union
end EtcdGrove
end Perennial
