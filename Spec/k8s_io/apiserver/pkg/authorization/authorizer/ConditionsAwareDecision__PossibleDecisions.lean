/-
`d.PossibleDecisions()` (`conditions.go`): a new set of `d`'s possible decisions, `m.pd`.
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
abbrev ConditionsAwareDecision.PossibleDecisions.spec : Prop :=
  ∀ (d : ConditionsAwareDecision) (m : Dec),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.authorization.authorizer ∗ isDecision d m }}
    (App (Val (d @!! ConditionsAwareDecision.ty @!! go!"PossibleDecisions")) (Val #()))
  {{ (s : Loc), RET #s; ∃ S : GMap w64 sets.Elem, s ↦$ S ∗ ⌜setIs S m.pd⌝ }}

end spec

end authorizer
end EtcdGrove
end Perennial
