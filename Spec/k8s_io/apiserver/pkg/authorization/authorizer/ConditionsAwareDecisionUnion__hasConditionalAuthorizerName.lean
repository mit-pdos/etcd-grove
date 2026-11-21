/-
`u.hasConditionalAuthorizerName(name)` (`conditionsunion.go`): whether a child has the name.
Lean-first (no Rocq counterpart).
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
abbrev ConditionsAwareDecisionUnion.hasConditionalAuthorizerName.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (u : ConditionsAwareDecisionUnion) (dq' : DFrac) (nds : List namedConditionsAwareDecision)
    (name : GoString),
  {{ (p ↦{dq} u ∗ u.inner' ↦*{dq'} nds : IProp GF) }}
    (App (Val (p @!! go.GoType.PointerType ConditionsAwareDecisionUnion.ty @!! go!"hasConditionalAuthorizerName")) (Val #name))
  {{ (b : Bool), RET #b; p ↦{dq} u ∗ u.inner' ↦*{dq'} nds }}

end spec

end authorizer
end EtcdGrove
end Perennial
