/-
The proof of `ConditionEvaluationResultError.spec`
(`Spec/k8s_io/apiserver/pkg/authorization/authorizer/ConditionEvaluationResultError.lean`).
Lean-first (no Rocq counterpart).
-/
module

public import Proof.k8s_io.apimachinery.pkg.util.errors.ErrTreeOk
public import Perennial.Proof.errors.NewVar
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionEvaluationResultError
public import Perennial.Spec.errors.New

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

theorem ConditionEvaluationResultError.wp_proof
    (wp_errors_New : _root_.Perennial.errors.New.spec (GF := GF) (hG := hG)) :
    ConditionEvaluationResultError.spec (GF := GF) (hG := hG) := by
  intro e
  wp_start as #He
  wp_auto
  cases e with
  | ok ei =>
    wp_auto
    iapply HΦ
    iexact He
  | nil =>
    wp_auto
    wp_apply _root_.Perennial.errors.wp_New_errorString as %x ⟨#_, #Hx⟩
    iapply HΦ
    iapply utilerrors.errorString_errTreeOrNil x _
    iexact Hx

end proof

end authorizer
end EtcdGrove
end Perennial
