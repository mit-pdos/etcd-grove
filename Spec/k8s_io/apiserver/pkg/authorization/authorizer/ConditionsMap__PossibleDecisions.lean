/-
`c.PossibleDecisions()` (`conditionsmap.go`): a new set of NoOpinion, Allow if there is an Allow
condition, Deny if there is a Deny condition. Lean-first (no Rocq counterpart).
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
abbrev ConditionsMap.PossibleDecisions.spec : Prop :=
  ∀ (c : ConditionsMap) (dq dq' : DFrac) (dn al : List GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.authorization.authorizer ∗ c.denyConditions' ↦*{dq} dn ∗ c.allowConditions' ↦*{dq'} al }}
    (App (Val (c @!! ConditionsMap.ty @!! go!"PossibleDecisions")) (Val #()))
  {{ (s : Loc), RET #s; (∃ S : GMap w64 sets.Elem, s ↦$ S ∗ ⌜setIs S (Dec.cmap dn [] al).pd⌝) ∗
      c.denyConditions' ↦*{dq} dn ∗ c.allowConditions' ↦*{dq'} al }}

end spec

end authorizer
end EtcdGrove
end Perennial
