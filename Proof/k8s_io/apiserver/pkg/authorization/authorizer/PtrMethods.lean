/-
Lean-first (no Rocq counterpart).

The `*ConditionsAwareDecision` method set's wrappers of `ConditionsAwareDecision`'s value methods
(Go calls `d.IsAllow()` on an addressable `d` through them: goose's `ptr_unfold'IsAllow`, ...): the
value method on `*l`, from its spec (`X_of`, a hypothesis), as `sets/PtrMethods.lean` does for
`Set[T]`. For the proofs of the callers, which hold their decision in a local variable.
-/
module

public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__IsAllow
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__IsDeny
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__IsNoOpinion
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__IsConditionsMap
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__IsUnion
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__PossibleDecisions
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__FailureDecision

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace authorizer

open Iris Iris.BI Iris.ProofMode k8s_io.apiserver.pkg.authorization.authorizer

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.authorization.authorizer.Assumptions]

/-- `(*ConditionsAwareDecision).IsAllow` on the decision `*l`. -/
theorem ConditionsAwareDecision.wp_ptr_IsAllow_of
    (wp_IsAllow : ConditionsAwareDecision.IsAllow.spec (GF := GF) (hG := hG))
    (l : Loc) (dl : DFrac) (d : ConditionsAwareDecision) :
    {{ (l ↦{dl} d : IProp GF) }}
      (App (Val (l @!! go.GoType.PointerType ConditionsAwareDecision.ty @!! go!"IsAllow")) (Val #()))
    {{ RET #(decide (d.decisionType' = W64 11)); l ↦{dl} d }} := by
  wp_start as Hl
  wp_auto
  wp_apply (wp_IsAllow d)
  iapply HΦ; iframe

/-- `(*ConditionsAwareDecision).PossibleDecisions` on the decision `*l`. -/
theorem ConditionsAwareDecision.wp_ptr_PossibleDecisions_of
    (wp_PossibleDecisions : ConditionsAwareDecision.PossibleDecisions.spec (GF := GF) (hG := hG))
    (l : Loc) (dl : DFrac) (d : ConditionsAwareDecision) (m : Dec) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.authorization.authorizer ∗
        l ↦{dl} d ∗ isDecision d m }}
      (App (Val (l @!! go.GoType.PointerType ConditionsAwareDecision.ty @!! go!"PossibleDecisions"))
        (Val #()))
    {{ (s : Loc), RET #s; (∃ S : GMap w64 sets.Elem, s ↦$ S ∗ ⌜setIs S m.pd⌝) ∗ l ↦{dl} d }} := by
  iintro %Φ ⟨#Hpkg, Hl, #Hd⟩ HΦ
  wp_method_call; (try wp_call)
  wp_auto
  iapply (wp_PossibleDecisions d m)
  · iframe #
  iintro !> %s HS
  iapply HΦ
  iframe

/-- `(*ConditionsAwareDecision).FailureDecision` on the decision `*l`. -/
theorem ConditionsAwareDecision.wp_ptr_FailureDecision_of
    (wp_FailureDecision : ConditionsAwareDecision.FailureDecision.spec (GF := GF) (hG := hG))
    (l : Loc) (dl : DFrac) (d : ConditionsAwareDecision) (m : Dec) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.authorization.authorizer ∗
        l ↦{dl} d ∗ isDecision d m }}
      (App (Val (l @!! go.GoType.PointerType ConditionsAwareDecision.ty @!! go!"FailureDecision"))
        (Val #()))
    {{ RET #(m.pd.failure); l ↦{dl} d }} := by
  iintro %Φ ⟨#Hpkg, Hl, #Hd⟩ HΦ
  wp_method_call; (try wp_call)
  wp_auto
  iapply (wp_FailureDecision d m)
  · iframe #
  iintro !> -
  iapply HΦ
  iframe

end wps

end authorizer
end EtcdGrove
end Perennial
