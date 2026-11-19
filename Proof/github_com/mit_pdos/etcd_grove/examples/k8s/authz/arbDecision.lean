/-
The proof of `arbDecision.spec`
(`Spec/github_com/mit_pdos/etcd_grove/examples/k8s/authz/arbDecision.lean`). Lean-first (no Rocq
counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.authz.arbDecision
public import Spec.math.rand.Int63n
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.authz.arbReason
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.authz.arbErr
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecisionDeny
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecisionAllow
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecisionNoOpinion
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.authz.arbConds
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecisionConditionsMap
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.authz.arbName
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecisionUnion__Add
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecisionUnion__ToDecision

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

theorem arbDecision.wp_proof
    (wp_Int63n : EtcdGrove.rand.Int63n.spec (GF := GF) (hG := hG))
    (wp_arbReason : EtcdGrove.k8s_authz.arbReason.spec (GF := GF) (hG := hG))
    (wp_arbErr : EtcdGrove.k8s_authz.arbErr.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecisionDeny : EtcdGrove.authorizer.ConditionsAwareDecisionDeny.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecisionAllow : EtcdGrove.authorizer.ConditionsAwareDecisionAllow.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecisionNoOpinion : EtcdGrove.authorizer.ConditionsAwareDecisionNoOpinion.spec (GF := GF) (hG := hG))
    (wp_arbConds : EtcdGrove.k8s_authz.arbConds.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecisionConditionsMap : EtcdGrove.authorizer.ConditionsAwareDecisionConditionsMap.spec (GF := GF) (hG := hG))
    (wp_arbName : EtcdGrove.k8s_authz.arbName.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecisionUnion_Add : EtcdGrove.authorizer.ConditionsAwareDecisionUnion.Add.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecisionUnion_ToDecision : EtcdGrove.authorizer.ConditionsAwareDecisionUnion.ToDecision.spec (GF := GF) (hG := hG)) :
    arbDecision.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end k8s_authz
end EtcdGrove
end Perennial
