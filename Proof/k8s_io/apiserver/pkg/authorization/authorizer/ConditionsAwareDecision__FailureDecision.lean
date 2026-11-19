/-
The proof of `ConditionsAwareDecision.FailureDecision.spec` (`Spec/k8s_io/apiserver/pkg/authorizat
ion/authorizer/ConditionsAwareDecision__FailureDecision.lean`). Lean-first (no Rocq counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__FailureDecision
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__PossibleDecisions
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

theorem ConditionsAwareDecision.FailureDecision.wp_proof
    (wp_ConditionsAwareDecision_PossibleDecisions : EtcdGrove.authorizer.ConditionsAwareDecision.PossibleDecisions.spec (GF := GF) (hG := hG))
    (wp_Set__Has : EtcdGrove.sets.Set.Has.spec (GF := GF) (hG := hG)) :
    ConditionsAwareDecision.FailureDecision.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end authorizer
end EtcdGrove
end Perennial
