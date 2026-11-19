/-
The proof of `ConditionsEvaluationResultUnevaluatable.spec` (`Spec/k8s_io/apiserver/pkg/authorizat
ion/authorizer/ConditionsEvaluationResultUnevaluatable.lean`). Lean-first (no Rocq counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsEvaluationResultUnevaluatable

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

theorem ConditionsEvaluationResultUnevaluatable.wp_proof :
    ConditionsEvaluationResultUnevaluatable.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_auto
  iapply HΦ
  itrivial

end proof

end authorizer
end EtcdGrove
end Perennial
