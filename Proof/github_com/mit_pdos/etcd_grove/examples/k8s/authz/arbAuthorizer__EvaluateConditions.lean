/-
The proof of `arbAuthorizer.EvaluateConditions.spec`
(`Spec/github_com/mit_pdos/etcd_grove/examples/k8s/authz/arbAuthorizer__EvaluateConditions.lean`).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.authz.arbAuthorizer__EvaluateConditions
public import Spec.math.rand.Int63n
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.authz.arbDecisionValue
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.authz.arbReason
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.authz.arbErr
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.authz.arbMaybeEval
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.PartiallyEvaluateConditionsAwareDecision
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__UnconditionalPartsOrFailClosed
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__IsConditionsMap
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__ConditionsMap
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.authz.arbEval
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsMap__Evaluate
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__FailureDecision

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

theorem arbAuthorizer.EvaluateConditions.wp_proof
    (wp_Int63n : EtcdGrove.rand.Int63n.spec (GF := GF) (hG := hG))
    (wp_arbDecisionValue : EtcdGrove.k8s_authz.arbDecisionValue.spec (GF := GF) (hG := hG))
    (wp_arbReason : EtcdGrove.k8s_authz.arbReason.spec (GF := GF) (hG := hG))
    (wp_arbErr : EtcdGrove.k8s_authz.arbErr.spec (GF := GF) (hG := hG))
    (wp_arbMaybeEval : EtcdGrove.k8s_authz.arbMaybeEval.spec (GF := GF) (hG := hG))
    (wp_PartiallyEvaluateConditionsAwareDecision : EtcdGrove.authorizer.PartiallyEvaluateConditionsAwareDecision.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecision_UnconditionalPartsOrFailClosed : EtcdGrove.authorizer.ConditionsAwareDecision.UnconditionalPartsOrFailClosed.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecision_IsConditionsMap : EtcdGrove.authorizer.ConditionsAwareDecision.IsConditionsMap.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecision_ConditionsMap : EtcdGrove.authorizer.ConditionsAwareDecision.ConditionsMap.spec (GF := GF) (hG := hG))
    (wp_arbEval : EtcdGrove.k8s_authz.arbEval.spec (GF := GF) (hG := hG))
    (wp_ConditionsMap_Evaluate : EtcdGrove.authorizer.ConditionsMap.Evaluate.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecision_FailureDecision : EtcdGrove.authorizer.ConditionsAwareDecision.FailureDecision.spec (GF := GF) (hG := hG)) :
    arbAuthorizer.EvaluateConditions.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end k8s_authz
end EtcdGrove
end Perennial
