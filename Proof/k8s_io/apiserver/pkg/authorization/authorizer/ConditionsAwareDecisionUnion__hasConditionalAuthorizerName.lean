/-
The proof of `ConditionsAwareDecisionUnion.hasConditionalAuthorizerName.spec` (`Spec/k8s_io/apiser
ver/pkg/authorization/authorizer/ConditionsAwareDecisionUnion__hasConditionalAuthorizerName.lean`)
. Lean-first (no Rocq counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecisionUnion__hasConditionalAuthorizerName
public import Spec.slices.ContainsFunc

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

theorem ConditionsAwareDecisionUnion.hasConditionalAuthorizerName.wp_proof
    (wp_ContainsFunc : EtcdGrove.slices.ContainsFunc.spec (GF := GF) (hG := hG)) :
    ConditionsAwareDecisionUnion.hasConditionalAuthorizerName.spec (GF := GF) (hG := hG) := by
  intro p dq u dq' nds name
  wp_start as ⟨Hp, Hs⟩
  icases (ConditionsAwareDecisionUnion.access_load'ConditionsAwareDecisionUnion'inner p u dq).access_strict
    $$ Hp with ⟨Hi, Hclose⟩
  wp_auto
  ipersist conditionalAuthorizerName
  wp_apply (wp_ContainsFunc u.inner' dq' nds) $$ [$Hs] as %b Hs
  · iintro !> %x %Hx
    wp_start
    wp_auto
    iapply HΦ
    itrivial
  iapply HΦ
  iframe Hs
  iapply Hclose $$ Hi

end proof

end authorizer
end EtcdGrove
end Perennial
