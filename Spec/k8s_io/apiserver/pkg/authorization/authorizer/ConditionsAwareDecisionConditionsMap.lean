/-
`ConditionsAwareDecisionConditionsMap(deny, noOpinion, allow)` (`conditionsmap.go`): a well-formed
leaf decision (depth `0`: a conditions map of copies of the slices, or an unconditional decision when the map
would be empty, too large, without Allow and Deny conditions, or invalid), for conditions that can
be called. Lean-first (no Rocq counterpart).
-/
module

public import Proof.k8s_io.apiserver.pkg.authorization.authorizer.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace authorizer

open Iris Iris.BI k8s_io.apiserver.pkg.authorization.authorizer

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.authorization.authorizer.Assumptions]

/-- See the file header. -/
abbrev ConditionsAwareDecisionConditionsMap.spec : Prop :=
  ∀ (sd sn sa : GoSlice) (qd qn qa : DFrac) (dn no al : List GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.authorization.authorizer ∗ sd ↦*{qd} dn ∗ sn ↦*{qn} no ∗ sa ↦*{qa} al ∗
      [∗list] c ∈ dn ++ no ++ al, isCondition c }}
    (App (App (App (Val (@! ConditionsAwareDecisionConditionsMap)) (Val #sd)) (Val #sn)) (Val #sa))
  {{ (d : ConditionsAwareDecision), RET #d; isWFDecisionLe 0 d ∗ sd ↦*{qd} dn ∗ sn ↦*{qn} no ∗ sa ↦*{qa} al }}

end spec

end authorizer
end EtcdGrove
end Perennial
