/-
`u.ToDecision()` (`conditionsunion.go`): a well-formed decision (a union of copies of the
children, or an unconditional decision when the builder recorded errors or the union has one
possible outcome), no deeper and no larger (`Dec.size`) than the union of the children, its names
the children's; the builder is unchanged. The union of the children fits `strings.Join`
(`Dec.foldFits`): the unconditional decision's reason joins one string per collected leaf
(fmt stage 1). Lean-first (no Rocq counterpart).
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
abbrev ConditionsAwareDecisionUnion.ToDecision.spec : Prop :=
  ∀ (p : Loc) (ks : List Dec) (N : Nat), Dec.foldFits N (.union ks) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.authorization.authorizer ∗ ownBuilder p ks N }}
    (App (Val (p @!! go.GoType.PointerType ConditionsAwareDecisionUnion.ty @!! go!"ToDecision")) (Val #()))
  {{ (d : ConditionsAwareDecision), RET #d;
      isWFDecisionBnd (Dec.depthL ks + 1) (Dec.sizeL ks + 1) N d ∗ ownBuilder p ks N }}

end spec

end authorizer
end EtcdGrove
end Perennial
