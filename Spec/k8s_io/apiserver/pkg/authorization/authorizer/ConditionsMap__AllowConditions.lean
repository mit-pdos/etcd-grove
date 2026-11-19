/-
`c.AllowConditions()` (`conditionsmap.go`): an iterator over `c.allowConditions`. Lean-first (no
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
abbrev ConditionsMap.AllowConditions.spec : Prop :=
  ∀ (c : ConditionsMap) (dq : DFrac) (cs : List GoInterface),
  {{ (c.allowConditions' ↦*{dq} cs : IProp GF) }}
    (App (Val (c @!! ConditionsMap.ty @!! go!"AllowConditions")) (Val #()))
  {{ (f : GoFunc), RET #f; c.allowConditions' ↦*{dq} cs ∗ seqOk (GF := GF) f cs }}

end spec

end authorizer
end EtcdGrove
end Perennial
