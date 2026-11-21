/-
`u.ContainsUnconditionalAllowOrDeny()` (`conditionsunion.go`): the memoized flag. Lean-first (no
Rocq counterpart).
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
abbrev ConditionsAwareDecisionUnion.ContainsUnconditionalAllowOrDeny.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (u : ConditionsAwareDecisionUnion),
  {{ (p ↦{dq} u : IProp GF) }}
    (App (Val (p @!! go.GoType.PointerType ConditionsAwareDecisionUnion.ty @!! go!"ContainsUnconditionalAllowOrDeny")) (Val #()))
  {{ RET #(u.containsUnconditionalAllowOrDeny'); p ↦{dq} u }}

end spec

end authorizer
end EtcdGrove
end Perennial
