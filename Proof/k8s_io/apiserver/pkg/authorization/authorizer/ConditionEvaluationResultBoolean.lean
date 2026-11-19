/-
The proof of `ConditionEvaluationResultBoolean.spec`
(`Spec/k8s_io/apiserver/pkg/authorization/authorizer/ConditionEvaluationResultBoolean.lean`).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionEvaluationResultBoolean

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

theorem ConditionEvaluationResultBoolean.wp_proof :
    ConditionEvaluationResultBoolean.spec (GF := GF) (hG := hG) := by
  intro b
  wp_start
  cases b <;> simp only [ite_true, Bool.false_eq_true, ite_false] <;> wp_auto <;> iapply HΦ <;> itrivial

end proof

end authorizer
end EtcdGrove
end Perennial
