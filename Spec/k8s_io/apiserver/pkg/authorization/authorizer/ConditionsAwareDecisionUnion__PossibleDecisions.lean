/-
`u.PossibleDecisions()` (`conditionsunion.go`): a new set of the possible decisions of a union of
the children `ks` (`subOk`: the memoized fields agree with `ks`), whether `u` is a builder (its
set owned) or a decision's union field (its set read-only). Lean-first (no Rocq counterpart).
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
abbrev ConditionsAwareDecisionUnion.PossibleDecisions.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (u : ConditionsAwareDecisionUnion) (dq' : DFrac) (ks : List Dec),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.authorization.authorizer ∗ p ↦{dq} u ∗ subOk u dq' ks }}
    (App (Val (p @!! go.GoType.PointerType ConditionsAwareDecisionUnion.ty @!! go!"PossibleDecisions")) (Val #()))
  {{ (s : Loc), RET #s; (∃ S : GMap w64 sets.Elem, s ↦$ S ∗ ⌜setIs S (Dec.union ks).pd⌝) ∗
      p ↦{dq} u ∗ subOk u dq' ks }}

end spec

end authorizer
end EtcdGrove
end Perennial
