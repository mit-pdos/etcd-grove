/-
The proof of `ConditionEvaluationResult.IsError.spec`
(`Spec/k8s_io/apiserver/pkg/authorization/authorizer/ConditionEvaluationResult__IsError.lean`).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionEvaluationResult__IsError

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

theorem ConditionEvaluationResult.IsError.wp_proof :
    ConditionEvaluationResult.IsError.spec (GF := GF) (hG := hG) := by
  intro r
  wp_start
  wp_auto
  iapply HΦ
  itrivial

end proof

end authorizer
end EtcdGrove
end Perennial
