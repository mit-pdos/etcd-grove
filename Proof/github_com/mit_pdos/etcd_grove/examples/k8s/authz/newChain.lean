/-
The proof of `newChain.spec`
(`Spec/github_com/mit_pdos/etcd_grove/examples/k8s/authz/newChain.lean`). Lean-first (no Rocq
counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.authz.newChain
public import Spec.k8s_io.apiserver.pkg.authorization.union.New
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.authz.arbAuthorizer__ConditionsAwareAuthorize
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.authz.arbAuthorizer__EvaluateConditions
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.AuthorizerFunc__ConditionsAwareAuthorize
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.AuthorizerFunc__EvaluateConditions
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.authz.legacyAuthorize

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

theorem newChain.wp_proof
    (wp_New : EtcdGrove.union.New.spec (GF := GF) (hG := hG))
    (wp_arbAuthorizer_ConditionsAwareAuthorize : EtcdGrove.k8s_authz.arbAuthorizer.ConditionsAwareAuthorize.spec (GF := GF) (hG := hG))
    (wp_arbAuthorizer_EvaluateConditions : EtcdGrove.k8s_authz.arbAuthorizer.EvaluateConditions.spec (GF := GF) (hG := hG))
    (wp_AuthorizerFunc_ConditionsAwareAuthorize : EtcdGrove.authorizer.AuthorizerFunc.ConditionsAwareAuthorize.spec (GF := GF) (hG := hG))
    (wp_AuthorizerFunc_EvaluateConditions : EtcdGrove.authorizer.AuthorizerFunc.EvaluateConditions.spec (GF := GF) (hG := hG))
    (wp_legacyAuthorize : EtcdGrove.k8s_authz.legacyAuthorize.spec (GF := GF) (hG := hG)) :
    newChain.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end k8s_authz
end EtcdGrove
end Perennial
