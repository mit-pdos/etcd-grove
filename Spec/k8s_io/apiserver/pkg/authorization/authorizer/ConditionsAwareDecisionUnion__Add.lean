/-
`u.Add(name, d)` (`conditionsunion.go`): `d` (well-formed, less than `2 ^ 63 - 1` deep: `ownBuilder`)
appended to the builder's children,
unless they already contain an unconditional Allow or Deny (invalid names are recorded as errors).
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
abbrev ConditionsAwareDecisionUnion.Add.spec : Prop :=
  ∀ (p : Loc) (ks : List Dec) (name : GoString) (d : ConditionsAwareDecision) (m : Dec),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.authorization.authorizer ∗ ownBuilder p ks ∗ isDecision d m ∗ ⌜m.WF ∧ m.depth + 1 < 2 ^ 63⌝ }}
    (App (App (Val (p @!! go.GoType.PointerType ConditionsAwareDecisionUnion.ty @!! go!"Add")) (Val #name)) (Val #d))
  {{ RET #(); ownBuilder p (if Dec.cuadL ks then ks else ks ++ [m]) }}

end spec

end authorizer
end EtcdGrove
end Perennial
