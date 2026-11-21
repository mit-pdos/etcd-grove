/-
The proof of `ConditionsAwareDecisionNoOpinion.spec`
(`Spec/k8s_io/apiserver/pkg/authorization/authorizer/ConditionsAwareDecisionNoOpinion.lean`).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecisionNoOpinion

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

theorem ConditionsAwareDecisionNoOpinion.wp_proof :
    ConditionsAwareDecisionNoOpinion.spec (GF := GF) (hG := hG) := by
  intro r e
  wp_start as #He
  wp_auto
  iapply HΦ
  unfold isDecision isDecisionRaw
  iintro !>
  isplitr
  · ipureintro; rfl
  · iexact He

end proof

end authorizer
end EtcdGrove
end Perennial
