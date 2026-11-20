/-
`validateConditions(seenIDs, conditions)` (`conditionsmap.go`): some error, the seen IDs updated,
for conditions that can be called. Lean-first (no Rocq counterpart).
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
abbrev validateConditions.spec : Prop :=
  ∀ (seen : Loc) (S : GMap GoString sets.Elem) (s : GoSlice) (dq : DFrac) (cs : List GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.authorization.authorizer ∗ seen ↦$ S ∗ s ↦*{dq} cs ∗ [∗list] c ∈ cs, isCondition c }}
    (App (App (Val (@! validateConditions)) (Val #seen)) (Val #s))
  {{ (e : GoInterface), RET #e; (∃ S' : GMap GoString sets.Elem, seen ↦$ S') ∗ s ↦*{dq} cs }}

end spec

end authorizer
end EtcdGrove
end Perennial
