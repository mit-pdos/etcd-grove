/-
The proof of `unionAuthzHandler.EvaluateConditions.spec`
(`Spec/k8s_io/apiserver/pkg/authorization/union/unionAuthzHandler__EvaluateConditions.lean`).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.authorization.union.unionAuthzHandler__EvaluateConditions
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__IsUnion
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__FailureDecision
public import Perennial.Spec.errors.New
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__UnionedDecisions
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__IsDeny
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__Reason
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__Error
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__IsAllow
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__IsNoOpinion
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__IsConditionsMap
public import Spec.k8s_io.apiserver.pkg.authorization.union.unionAuthzHandler__evaluateConditions
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__PossibleDecisions
public import Spec.k8s_io.apimachinery.pkg.util.sets.Set__Has
public import Spec.k8s_io.apimachinery.pkg.util.sets.ListW
public import Spec.fmt.ErrorfAny
public import Perennial.Spec.fmt.Sprintf
public import Perennial.Spec.strings.Join
public import Spec.k8s_io.apimachinery.pkg.util.errors.NewAggregate

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace union

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode k8s_io.apiserver.pkg.authorization.authorizer k8s_io.apiserver.pkg.authorization.union EtcdGrove.authorizer

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.authorization.union.Assumptions]

theorem unionAuthzHandler.EvaluateConditions.wp_proof
    (wp_ConditionsAwareDecision_IsUnion : EtcdGrove.authorizer.ConditionsAwareDecision.IsUnion.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecision_FailureDecision : EtcdGrove.authorizer.ConditionsAwareDecision.FailureDecision.spec (GF := GF) (hG := hG))
    (wp_errors_New : _root_.Perennial.errors.New.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecision_UnionedDecisions : EtcdGrove.authorizer.ConditionsAwareDecision.UnionedDecisions.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecision_IsDeny : EtcdGrove.authorizer.ConditionsAwareDecision.IsDeny.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecision_Reason : EtcdGrove.authorizer.ConditionsAwareDecision.Reason.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecision_Error : EtcdGrove.authorizer.ConditionsAwareDecision.Error.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecision_IsAllow : EtcdGrove.authorizer.ConditionsAwareDecision.IsAllow.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecision_IsNoOpinion : EtcdGrove.authorizer.ConditionsAwareDecision.IsNoOpinion.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecision_IsConditionsMap : EtcdGrove.authorizer.ConditionsAwareDecision.IsConditionsMap.spec (GF := GF) (hG := hG))
    (wp_unionAuthzHandler_evaluateConditions : EtcdGrove.union.unionAuthzHandler.evaluateConditions.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecision_PossibleDecisions : EtcdGrove.authorizer.ConditionsAwareDecision.PossibleDecisions.spec (GF := GF) (hG := hG))
    (wp_Set__Has : EtcdGrove.sets.Set.Has.spec (GF := GF) (hG := hG))
    (wp_List : EtcdGrove.sets.List'.specW (GF := GF) (hG := hG))
    (wp_ErrorfAny : EtcdGrove.fmt.ErrorfAny.spec (GF := GF) (hG := hG))
    (wp_Sprintf : _root_.Perennial.fmt.Sprintf.spec (GF := GF) (hG := hG))
    (wp_Join : _root_.Perennial.strings.Join.spec (GF := GF) (hG := hG))
    (wp_NewAggregate : EtcdGrove.utilerrors.NewAggregate.spec (GF := GF) (hG := hG)) :
    unionAuthzHandler.EvaluateConditions.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end union
end EtcdGrove
end Perennial
