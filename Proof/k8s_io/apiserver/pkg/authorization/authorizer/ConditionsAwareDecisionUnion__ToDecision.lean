/-
The proof of `ConditionsAwareDecisionUnion.ToDecision.spec` (`Spec/k8s_io/apiserver/pkg/authorizat
ion/authorizer/ConditionsAwareDecisionUnion__ToDecision.lean`). Lean-first (no Rocq counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecisionUnion__ToDecision
public import Spec.k8s_io.apimachinery.pkg.util.errors.NewAggregate
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecisionUnion__FailureDecision
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecisionFromParts
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecisionUnion__PossibleDecisions
public import Spec.k8s_io.apimachinery.pkg.util.sets.Set__Len
public import Spec.k8s_io.apimachinery.pkg.util.sets.Set__UnsortedList
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.collectReasonsAndErrors
public import Perennial.Spec.strings.Join
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecisionDeny
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecisionNoOpinion
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecisionAllow
public import Perennial.Spec.errors.New
public import Spec.slices.Clone
public import Spec.k8s_io.apimachinery.pkg.util.sets.Set__Clone

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

theorem ConditionsAwareDecisionUnion.ToDecision.wp_proof
    (wp_NewAggregate : EtcdGrove.utilerrors.NewAggregate.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecisionUnion_FailureDecision : EtcdGrove.authorizer.ConditionsAwareDecisionUnion.FailureDecision.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecisionFromParts : EtcdGrove.authorizer.ConditionsAwareDecisionFromParts.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecisionUnion_PossibleDecisions : EtcdGrove.authorizer.ConditionsAwareDecisionUnion.PossibleDecisions.spec (GF := GF) (hG := hG))
    (wp_Set__Len : EtcdGrove.sets.Set.Len.spec (GF := GF) (hG := hG))
    (wp_Set__UnsortedList : EtcdGrove.sets.Set.UnsortedList.spec (GF := GF) (hG := hG))
    (wp_collectReasonsAndErrors : EtcdGrove.authorizer.collectReasonsAndErrors.spec (GF := GF) (hG := hG))
    (wp_Join : _root_.Perennial.strings.Join.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecisionDeny : EtcdGrove.authorizer.ConditionsAwareDecisionDeny.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecisionNoOpinion : EtcdGrove.authorizer.ConditionsAwareDecisionNoOpinion.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecisionAllow : EtcdGrove.authorizer.ConditionsAwareDecisionAllow.spec (GF := GF) (hG := hG))
    (wp_errors_New : _root_.Perennial.errors.New.spec (GF := GF) (hG := hG))
    (wp_Clone : EtcdGrove.slices.Clone.spec (GF := GF) (hG := hG))
    (wp_Set_Clone : EtcdGrove.sets.Set.Clone.spec (GF := GF) (hG := hG)) :
    ConditionsAwareDecisionUnion.ToDecision.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end authorizer
end EtcdGrove
end Perennial
