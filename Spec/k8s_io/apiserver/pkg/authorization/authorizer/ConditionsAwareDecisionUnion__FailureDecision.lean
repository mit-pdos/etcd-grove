/-
`u.FailureDecision()` (`conditionsunion.go`): Deny if Deny is possible, else NoOpinion. Lean-first
(no Rocq counterpart).
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
abbrev ConditionsAwareDecisionUnion.FailureDecision.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (u : ConditionsAwareDecisionUnion) (dq' : DFrac) (ks : List Dec),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.authorization.authorizer ∗ p ↦{dq} u ∗ subOk u dq' ks }}
    (App (Val (p @!! go.GoType.PointerType ConditionsAwareDecisionUnion.ty @!! go!"FailureDecision")) (Val #()))
  {{ RET #((Dec.union ks).pd.failure); p ↦{dq} u ∗ subOk u dq' ks }}

end spec

end authorizer
end EtcdGrove
end Perennial
