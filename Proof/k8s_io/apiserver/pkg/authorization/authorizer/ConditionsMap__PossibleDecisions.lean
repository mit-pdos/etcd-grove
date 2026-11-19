/-
The proof of `ConditionsMap.PossibleDecisions.spec`
(`Spec/k8s_io/apiserver/pkg/authorization/authorizer/ConditionsMap__PossibleDecisions.lean`).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsMap__PossibleDecisions
public import Spec.k8s_io.apimachinery.pkg.util.sets.New
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

theorem ConditionsMap.PossibleDecisions.wp_proof
    (wp_sets_New : EtcdGrove.sets.New.spec (GF := GF) (hG := hG))
    (wp_Set__Insert : EtcdGrove.sets.Set.Insert.spec (GF := GF) (hG := hG)) :
    ConditionsMap.PossibleDecisions.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end authorizer
end EtcdGrove
end Perennial
