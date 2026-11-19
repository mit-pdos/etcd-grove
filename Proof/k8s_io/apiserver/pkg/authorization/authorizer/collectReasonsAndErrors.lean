/-
The proof of `collectReasonsAndErrors.spec`
(`Spec/k8s_io/apiserver/pkg/authorization/authorizer/collectReasonsAndErrors.lean`). Lean-first
(no Rocq counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.collectReasonsAndErrors
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__IsAllow
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__IsNoOpinion
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__IsDeny
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__Reason
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__Error
public import Perennial.Spec.strings.Join
public import Perennial.Spec.fmt.Sprintf
public import Spec.fmt.ErrorfAny
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__IsUnion
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__UnionedDecisions
public import Spec.slices.Concat

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

theorem collectReasonsAndErrors.wp_proof
    (wp_ConditionsAwareDecision_IsAllow : EtcdGrove.authorizer.ConditionsAwareDecision.IsAllow.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecision_IsNoOpinion : EtcdGrove.authorizer.ConditionsAwareDecision.IsNoOpinion.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecision_IsDeny : EtcdGrove.authorizer.ConditionsAwareDecision.IsDeny.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecision_Reason : EtcdGrove.authorizer.ConditionsAwareDecision.Reason.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecision_Error : EtcdGrove.authorizer.ConditionsAwareDecision.Error.spec (GF := GF) (hG := hG))
    (wp_Join : _root_.Perennial.strings.Join.spec (GF := GF) (hG := hG))
    (wp_Sprintf : _root_.Perennial.fmt.Sprintf.spec (GF := GF) (hG := hG))
    (wp_ErrorfAny : EtcdGrove.fmt.ErrorfAny.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecision_IsUnion : EtcdGrove.authorizer.ConditionsAwareDecision.IsUnion.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecision_UnionedDecisions : EtcdGrove.authorizer.ConditionsAwareDecision.UnionedDecisions.spec (GF := GF) (hG := hG))
    (wp_Concat : EtcdGrove.slices.Concat.spec (GF := GF) (hG := hG)) :
    collectReasonsAndErrors.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end authorizer
end EtcdGrove
end Perennial
