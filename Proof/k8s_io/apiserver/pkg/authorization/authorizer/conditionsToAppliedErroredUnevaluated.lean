/-
The proof of `conditionsToAppliedErroredUnevaluated.spec`
(`Spec/k8s_io/apiserver/pkg/authorization/authorizer/conditionsToAppliedErroredUnevaluated.lean`).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.conditionsToAppliedErroredUnevaluated
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionEvaluationResult__IsTrue
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionEvaluationResult__IsFalse
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionEvaluationResult__IsUnevaluatable
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionEvaluationResult__IsError
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionEvaluationResult__Error
public import Perennial.Spec.fmt.Sprintf
public import Spec.fmt.ErrorfAny

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

theorem conditionsToAppliedErroredUnevaluated.wp_proof
    (wp_ConditionEvaluationResult_IsTrue : EtcdGrove.authorizer.ConditionEvaluationResult.IsTrue.spec (GF := GF) (hG := hG))
    (wp_ConditionEvaluationResult_IsFalse : EtcdGrove.authorizer.ConditionEvaluationResult.IsFalse.spec (GF := GF) (hG := hG))
    (wp_ConditionEvaluationResult_IsUnevaluatable : EtcdGrove.authorizer.ConditionEvaluationResult.IsUnevaluatable.spec (GF := GF) (hG := hG))
    (wp_ConditionEvaluationResult_IsError : EtcdGrove.authorizer.ConditionEvaluationResult.IsError.spec (GF := GF) (hG := hG))
    (wp_ConditionEvaluationResult_Error : EtcdGrove.authorizer.ConditionEvaluationResult.Error.spec (GF := GF) (hG := hG))
    (wp_Sprintf : _root_.Perennial.fmt.Sprintf.spec (GF := GF) (hG := hG))
    (wp_ErrorfAny : EtcdGrove.fmt.ErrorfAny.spec (GF := GF) (hG := hG)) :
    conditionsToAppliedErroredUnevaluated.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end authorizer
end EtcdGrove
end Perennial
