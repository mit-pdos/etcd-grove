/-
The proof of `ConditionsAwareDecisionUnion.Add.spec`
(`Spec/k8s_io/apiserver/pkg/authorization/authorizer/ConditionsAwareDecisionUnion__Add.lean`).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecisionUnion__Add
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecisionUnion__ContainsUnconditionalAllowOrDeny
public import Spec.fmt.ErrorfAny
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecisionUnion__hasConditionalAuthorizerName
public import Spec.k8s_io.apimachinery.pkg.util.validation.IsDNS1123Subdomain
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__ContainsUnconditionalAllowOrDeny
public import Spec.k8s_io.apimachinery.pkg.util.sets.New
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__PossibleDecisions
public import Spec.k8s_io.apimachinery.pkg.util.sets.Set__UnsortedList
public import Spec.k8s_io.apimachinery.pkg.util.sets.Set__Insert

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

theorem ConditionsAwareDecisionUnion.Add.wp_proof
    (wp_ConditionsAwareDecisionUnion_ContainsUnconditionalAllowOrDeny : EtcdGrove.authorizer.ConditionsAwareDecisionUnion.ContainsUnconditionalAllowOrDeny.spec (GF := GF) (hG := hG))
    (wp_ErrorfAny : EtcdGrove.fmt.ErrorfAny.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecisionUnion_hasConditionalAuthorizerName : EtcdGrove.authorizer.ConditionsAwareDecisionUnion.hasConditionalAuthorizerName.spec (GF := GF) (hG := hG))
    (wp_IsDNS1123Subdomain : EtcdGrove.validation.IsDNS1123Subdomain.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecision_ContainsUnconditionalAllowOrDeny : EtcdGrove.authorizer.ConditionsAwareDecision.ContainsUnconditionalAllowOrDeny.spec (GF := GF) (hG := hG))
    (wp_sets_New : EtcdGrove.sets.New.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecision_PossibleDecisions : EtcdGrove.authorizer.ConditionsAwareDecision.PossibleDecisions.spec (GF := GF) (hG := hG))
    (wp_Set__UnsortedList : EtcdGrove.sets.Set.UnsortedList.spec (GF := GF) (hG := hG))
    (wp_Set__Insert : EtcdGrove.sets.Set.Insert.spec (GF := GF) (hG := hG)) :
    ConditionsAwareDecisionUnion.Add.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end authorizer
end EtcdGrove
end Perennial
