/-
The proof of `arbResult.spec`
(`Spec/github_com/mit_pdos/etcd_grove/examples/k8s/authz/arbResult.lean`). Lean-first (no Rocq
counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.authz.arbResult
public import Spec.math.rand.Int63n
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionEvaluationResultBoolean
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.authz.arbErr
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionEvaluationResultError
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsEvaluationResultUnevaluatable

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

theorem arbResult.wp_proof
    (wp_Int63n : EtcdGrove.rand.Int63n.spec (GF := GF) (hG := hG))
    (wp_ConditionEvaluationResultBoolean : EtcdGrove.authorizer.ConditionEvaluationResultBoolean.spec (GF := GF) (hG := hG))
    (wp_arbErr : EtcdGrove.k8s_authz.arbErr.spec (GF := GF) (hG := hG))
    (wp_ConditionEvaluationResultError : EtcdGrove.authorizer.ConditionEvaluationResultError.spec (GF := GF) (hG := hG))
    (wp_ConditionsEvaluationResultUnevaluatable : EtcdGrove.authorizer.ConditionsEvaluationResultUnevaluatable.spec (GF := GF) (hG := hG)) :
    arbResult.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end k8s_authz
end EtcdGrove
end Perennial
