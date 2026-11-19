/-
The proof of `validateConditions.spec`
(`Spec/k8s_io/apiserver/pkg/authorization/authorizer/validateConditions.lean`). Lean-first (no
Rocq counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.validateConditions
public import Spec.k8s_io.apimachinery.pkg.util.sets.Set__Has
public import Spec.k8s_io.apimachinery.pkg.util.sets.Set__Insert
public import Spec.fmt.ErrorfAny
public import Spec.k8s_io.apimachinery.pkg.util.validation.field.NewPath
public import Spec.k8s_io.apimachinery.pkg.util.validation.IsDomainPrefixedKey
public import Spec.k8s_io.apimachinery.pkg.util.validation.field.ErrorList__ToAggregate

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

theorem validateConditions.wp_proof
    (wp_Set__Has : EtcdGrove.sets.Set.Has.spec (GF := GF) (hG := hG))
    (wp_Set__Insert : EtcdGrove.sets.Set.Insert.spec (GF := GF) (hG := hG))
    (wp_ErrorfAny : EtcdGrove.fmt.ErrorfAny.spec (GF := GF) (hG := hG))
    (wp_NewPath : EtcdGrove.field.NewPath.spec (GF := GF) (hG := hG))
    (wp_IsDomainPrefixedKey : EtcdGrove.validation.IsDomainPrefixedKey.spec (GF := GF) (hG := hG))
    (wp_ErrorList_ToAggregate : EtcdGrove.field.ErrorList.ToAggregate.spec (GF := GF) (hG := hG)) :
    validateConditions.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end authorizer
end EtcdGrove
end Perennial
