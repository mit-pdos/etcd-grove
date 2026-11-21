/-
`d.ContainsUnconditionalAllowOrDeny()` (`conditions.go`): whether `d`'s tree has an unconditional
Allow or Deny leaf (for a union, its memoized flag). Lean-first (no Rocq counterpart).
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
abbrev ConditionsAwareDecision.ContainsUnconditionalAllowOrDeny.spec : Prop :=
  ∀ (d : ConditionsAwareDecision) (m : Dec),
  {{ isDecision (GF := GF) d m }}
    (App (Val (d @!! ConditionsAwareDecision.ty @!! go!"ContainsUnconditionalAllowOrDeny")) (Val #()))
  {{ RET #(m.cuad); True }}

end spec

end authorizer
end EtcdGrove
end Perennial
