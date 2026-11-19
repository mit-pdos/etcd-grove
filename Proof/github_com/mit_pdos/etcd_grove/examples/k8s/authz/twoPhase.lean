/-
The proof of `twoPhase.spec`
(`Spec/github_com/mit_pdos/etcd_grove/examples/k8s/authz/twoPhase.lean`). Lean-first (no Rocq
counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.authz.twoPhase
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__PossibleDecisions
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__IsAllow
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__FailureDecision
public import Spec.k8s_io.apimachinery.pkg.util.sets.Set__Has
public import Spec.k8s_io.apiserver.pkg.authorization.union.unionAuthzHandler__EvaluateConditions

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_authz

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode k8s_io.apiserver.pkg.authorization.authorizer k8s_io.apiserver.pkg.authorization.union github_com.mit_pdos.etcd_grove.examples.k8s.authz EtcdGrove.authorizer EtcdGrove.union

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.authz.Assumptions]

theorem twoPhase.wp_proof
    (wp_ConditionsAwareDecision_PossibleDecisions : EtcdGrove.authorizer.ConditionsAwareDecision.PossibleDecisions.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecision_IsAllow : EtcdGrove.authorizer.ConditionsAwareDecision.IsAllow.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecision_FailureDecision : EtcdGrove.authorizer.ConditionsAwareDecision.FailureDecision.spec (GF := GF) (hG := hG))
    (wp_Set__Has : EtcdGrove.sets.Set.Has.spec (GF := GF) (hG := hG))
    (wp_unionAuthzHandler_EvaluateConditions : EtcdGrove.union.unionAuthzHandler.EvaluateConditions.spec (GF := GF) (hG := hG)) :
    twoPhase.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end k8s_authz
end EtcdGrove
end Perennial
