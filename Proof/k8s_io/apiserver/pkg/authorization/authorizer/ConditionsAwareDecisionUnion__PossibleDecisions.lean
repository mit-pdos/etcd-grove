/-
The proof of `ConditionsAwareDecisionUnion.PossibleDecisions.spec` (`Spec/k8s_io/apiserver/pkg/aut
horization/authorizer/ConditionsAwareDecisionUnion__PossibleDecisions.lean`). Lean-first (no Rocq
counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecisionUnion__PossibleDecisions
public import Spec.k8s_io.apimachinery.pkg.util.sets.New
public import Spec.k8s_io.apimachinery.pkg.util.sets.Set__UnsortedList
public import Spec.k8s_io.apimachinery.pkg.util.sets.Set__Insert
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecisionUnion__ContainsUnconditionalAllowOrDeny
public import Spec.k8s_io.apimachinery.pkg.util.sets.Set__Delete

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

theorem ConditionsAwareDecisionUnion.PossibleDecisions.wp_proof
    (wp_sets_New : EtcdGrove.sets.New.spec (GF := GF) (hG := hG))
    (wp_Set__UnsortedList : EtcdGrove.sets.Set.UnsortedList.spec (GF := GF) (hG := hG))
    (wp_Set__Insert : EtcdGrove.sets.Set.Insert.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecisionUnion_ContainsUnconditionalAllowOrDeny : EtcdGrove.authorizer.ConditionsAwareDecisionUnion.ContainsUnconditionalAllowOrDeny.spec (GF := GF) (hG := hG))
    (wp_Set__Delete : EtcdGrove.sets.Set.Delete.spec (GF := GF) (hG := hG)) :
    ConditionsAwareDecisionUnion.PossibleDecisions.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end authorizer
end EtcdGrove
end Perennial
