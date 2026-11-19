/-
The proof of `AuthorizerFunc.EvaluateConditions.spec`
(`Spec/k8s_io/apiserver/pkg/authorization/authorizer/AuthorizerFunc__EvaluateConditions.lean`).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.AuthorizerFunc__EvaluateConditions

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

theorem AuthorizerFunc.EvaluateConditions.wp_proof :
    AuthorizerFunc.EvaluateConditions.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end authorizer
end EtcdGrove
end Perennial
