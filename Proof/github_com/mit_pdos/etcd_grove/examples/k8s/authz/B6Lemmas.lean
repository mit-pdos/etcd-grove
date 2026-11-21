/-
Lean-first (no Rocq counterpart).

Lemmas of the driver's proofs (`examples/k8s/authz`): the case split of a `rand.Int63n(k)` result,
and the `*ConditionsAwareDecision` wrappers of the value methods `arbAuthorizer.EvaluateConditions`
calls on its (addressable) parameter that `authorizer/PtrMethods.lean` does not have, as there.
-/
module

public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__UnconditionalPartsOrFailClosed
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__IsConditionsMap
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__ConditionsMap

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_authz

open Iris Iris.BI Iris.ProofMode k8s_io.apiserver.pkg.authorization.authorizer EtcdGrove.authorizer

/-- A result of `rand.Int63n(4)`. -/
theorem int63n_4_cases (x : w64) (h : 0 ≤ sint.Z x ∧ sint.Z x < sint.Z (W64 4)) :
    x = W64 0 ∨ x = W64 1 ∨ x = W64 2 ∨ x = W64 3 := by
  have : sint.Z x = 0 ∨ sint.Z x = 1 ∨ sint.Z x = 2 ∨ sint.Z x = 3 := by
    have h4 : sint.Z (W64 4) = 4 := rfl
    have := h.2; rw [h4] at this; omega
  rcases this with h | h | h | h
  · left; word
  · right; left; word
  · right; right; left; word
  · right; right; right; word

/-- A result of `rand.Int63n(5)`. -/
theorem int63n_5_cases (x : w64) (h : 0 ≤ sint.Z x ∧ sint.Z x < sint.Z (W64 5)) :
    x = W64 0 ∨ x = W64 1 ∨ x = W64 2 ∨ x = W64 3 ∨ x = W64 4 := by
  have : sint.Z x = 0 ∨ sint.Z x = 1 ∨ sint.Z x = 2 ∨ sint.Z x = 3 ∨ sint.Z x = 4 := by
    have h5 : sint.Z (W64 5) = 5 := rfl
    have := h.2; rw [h5] at this; omega
  rcases this with h | h | h | h | h
  · left; word
  · right; left; word
  · right; right; left; word
  · right; right; right; left; word
  · right; right; right; right; word

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.authorization.authorizer.Assumptions]

/-- `(*ConditionsAwareDecision).IsConditionsMap` on the decision `*l`. -/
theorem wp_ptr_IsConditionsMap_of
    (wp_IsConditionsMap : ConditionsAwareDecision.IsConditionsMap.spec (GF := GF) (hG := hG))
    (l : Loc) (dl : DFrac) (d : ConditionsAwareDecision) :
    {{ (l ↦{dl} d : IProp GF) }}
      (App (Val (l @!! go.GoType.PointerType ConditionsAwareDecision.ty @!! go!"IsConditionsMap"))
        (Val #()))
    {{ RET #(decide (d.decisionType' = W64 13)); l ↦{dl} d }} := by
  wp_start as Hl
  wp_auto
  wp_apply (wp_IsConditionsMap d)
  iapply HΦ; iframe

/-- `(*ConditionsAwareDecision).ConditionsMap` on the decision `*l`. -/
theorem wp_ptr_ConditionsMap_of
    (wp_ConditionsMap : ConditionsAwareDecision.ConditionsMap.spec (GF := GF) (hG := hG))
    (l : Loc) (dl : DFrac) (d : ConditionsAwareDecision) :
    {{ (l ↦{dl} d : IProp GF) }}
      (App (Val (l @!! go.GoType.PointerType ConditionsAwareDecision.ty @!! go!"ConditionsMap"))
        (Val #()))
    {{ RET #(d.conditionsMap'); l ↦{dl} d }} := by
  wp_start as Hl
  wp_auto
  wp_apply (wp_ConditionsMap d)
  iapply HΦ; iframe

/-- `(*ConditionsAwareDecision).UnconditionalPartsOrFailClosed` on the decision `*l`. -/
theorem wp_ptr_UnconditionalPartsOrFailClosed_of
    (wp_UPFC : ConditionsAwareDecision.UnconditionalPartsOrFailClosed.spec (GF := GF) (hG := hG))
    (l : Loc) (dl : DFrac) (d : ConditionsAwareDecision) (m : Dec) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.authorization.authorizer ∗
        l ↦{dl} d ∗ isDecision d m }}
      (App (Val (l @!! go.GoType.PointerType ConditionsAwareDecision.ty
          @!! go!"UnconditionalPartsOrFailClosed")) (Val #()))
    {{ (dec : w64) (r : GoString) (e : GoInterface), RET (PairV (PairV #dec #r) #e); l ↦{dl} d }} := by
  iintro %Φ ⟨#Hpkg, Hl, #Hd⟩ HΦ
  wp_method_call; (try wp_call)
  wp_auto
  iapply (wp_UPFC d m)
  · iframe #
  iintro !> %dec %r %e _
  iapply HΦ
  iframe

end wps

end k8s_authz
end EtcdGrove
end Perennial
