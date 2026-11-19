/-
The proof of `AuthorizerFunc.ConditionsAwareAuthorize.spec` (`Spec/k8s_io/apiserver/pkg/authorizat
ion/authorizer/AuthorizerFunc__ConditionsAwareAuthorize.lean`). Lean-first (no Rocq counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.AuthorizerFunc__ConditionsAwareAuthorize
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.AuthorizerFunc__Authorize
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecisionFromParts

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

theorem AuthorizerFunc.ConditionsAwareAuthorize.wp_proof
    (wp_AuthorizerFunc_Authorize : EtcdGrove.authorizer.AuthorizerFunc.Authorize.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecisionFromParts : EtcdGrove.authorizer.ConditionsAwareDecisionFromParts.spec (GF := GF) (hG := hG)) :
    AuthorizerFunc.ConditionsAwareAuthorize.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end authorizer
end EtcdGrove
end Perennial
