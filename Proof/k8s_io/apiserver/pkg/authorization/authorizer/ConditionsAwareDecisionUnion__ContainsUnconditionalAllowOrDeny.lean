/-
The proof of `ConditionsAwareDecisionUnion.ContainsUnconditionalAllowOrDeny.spec` (`Spec/k8s_io/ap
iserver/pkg/authorization/authorizer/ConditionsAwareDecisionUnion__ContainsUnconditionalAllowOrDen
y.lean`). Lean-first (no Rocq counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecisionUnion__ContainsUnconditionalAllowOrDeny

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

theorem ConditionsAwareDecisionUnion.ContainsUnconditionalAllowOrDeny.wp_proof :
    ConditionsAwareDecisionUnion.ContainsUnconditionalAllowOrDeny.spec (GF := GF) (hG := hG) := by
  intro p dq u
  wp_start as Hp
  icases (ConditionsAwareDecisionUnion.access_load'ConditionsAwareDecisionUnion'containsUnconditionalAllowOrDeny
    p u dq).access_strict $$ Hp with ⟨Hf, Hclose⟩
  wp_auto
  iapply HΦ
  iapply Hclose
  iexact Hf

end proof

end authorizer
end EtcdGrove
end Perennial
