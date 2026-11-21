/-
Lean-first (no Rocq counterpart).

More of the `*ConditionsAwareDecision` method set's wrappers of `ConditionsAwareDecision`'s value
methods (as `PtrMethods.lean`), for `PartiallyEvaluateConditionsAwareDecision`'s proof, which holds
its decisions in local variables: `IsConditionsMap`, `ConditionsMap`, `IsUnion`, `UnionedDecisions`,
`ContainsUnconditionalAllowOrDeny`, `IsUnconditional` on `*l`, from their specs.
-/
module

public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__IsConditionsMap
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__ConditionsMap
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__IsUnion
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__UnionedDecisions
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__ContainsUnconditionalAllowOrDeny
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__IsUnconditional

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

/-- `(*ConditionsAwareDecision).IsConditionsMap` on the decision `*l`. -/
theorem ConditionsAwareDecision.wp_ptr_IsConditionsMap_of
    (wp_X : ConditionsAwareDecision.IsConditionsMap.spec (GF := GF) (hG := hG))
    (l : Loc) (dl : DFrac) (d : ConditionsAwareDecision) :
    {{ (l ↦{dl} d : IProp GF) }}
      (App (Val (l @!! go.GoType.PointerType ConditionsAwareDecision.ty @!! go!"IsConditionsMap")) (Val #()))
    {{ RET #(decide (d.decisionType' = W64 13)); l ↦{dl} d }} := by
  wp_start as Hl
  wp_auto
  wp_apply (wp_X d)
  iapply HΦ; iframe

/-- `(*ConditionsAwareDecision).ConditionsMap` on the decision `*l`. -/
theorem ConditionsAwareDecision.wp_ptr_ConditionsMap_of
    (wp_X : ConditionsAwareDecision.ConditionsMap.spec (GF := GF) (hG := hG))
    (l : Loc) (dl : DFrac) (d : ConditionsAwareDecision) :
    {{ (l ↦{dl} d : IProp GF) }}
      (App (Val (l @!! go.GoType.PointerType ConditionsAwareDecision.ty @!! go!"ConditionsMap")) (Val #()))
    {{ RET #(d.conditionsMap'); l ↦{dl} d }} := by
  wp_start as Hl
  wp_auto
  wp_apply (wp_X d)
  iapply HΦ; iframe

/-- `(*ConditionsAwareDecision).IsUnion` on the decision `*l`. -/
theorem ConditionsAwareDecision.wp_ptr_IsUnion_of
    (wp_X : ConditionsAwareDecision.IsUnion.spec (GF := GF) (hG := hG))
    (l : Loc) (dl : DFrac) (d : ConditionsAwareDecision) :
    {{ (l ↦{dl} d : IProp GF) }}
      (App (Val (l @!! go.GoType.PointerType ConditionsAwareDecision.ty @!! go!"IsUnion")) (Val #()))
    {{ RET #(decide (d.decisionType' = W64 14)); l ↦{dl} d }} := by
  wp_start as Hl
  wp_auto
  wp_apply (wp_X d)
  iapply HΦ; iframe

/-- `(*ConditionsAwareDecision).IsUnconditional` on the decision `*l`. -/
theorem ConditionsAwareDecision.wp_ptr_IsUnconditional_of
    (wp_X : ConditionsAwareDecision.IsUnconditional.spec (GF := GF) (hG := hG))
    (l : Loc) (dl : DFrac) (d : ConditionsAwareDecision) :
    {{ (l ↦{dl} d : IProp GF) }}
      (App (Val (l @!! go.GoType.PointerType ConditionsAwareDecision.ty @!! go!"IsUnconditional")) (Val #()))
    {{ RET #(decide (d.decisionType' = W64 11 ∨ d.decisionType' = W64 0 ∨
      d.decisionType' = W64 12)); l ↦{dl} d }} := by
  wp_start as Hl
  wp_auto
  wp_apply (wp_X d)
  iapply HΦ; iframe

/-- `(*ConditionsAwareDecision).ContainsUnconditionalAllowOrDeny` on the decision `*l`. -/
theorem ConditionsAwareDecision.wp_ptr_ContainsUnconditionalAllowOrDeny_of
    (wp_X : ConditionsAwareDecision.ContainsUnconditionalAllowOrDeny.spec (GF := GF) (hG := hG))
    (l : Loc) (dl : DFrac) (d : ConditionsAwareDecision) (m : Dec) :
    {{ l ↦{dl} d ∗ isDecision (GF := GF) d m }}
      (App (Val (l @!! go.GoType.PointerType ConditionsAwareDecision.ty @!! go!"ContainsUnconditionalAllowOrDeny")) (Val #()))
    {{ RET #(m.cuad); l ↦{dl} d }} := by
  iintro %Φ ⟨Hl, #Hd⟩ HΦ
  wp_method_call; (try wp_call)
  wp_auto
  iapply (wp_X d m)
  · iexact Hd
  iintro !> -
  iapply HΦ
  iframe

/-- `(*ConditionsAwareDecision).UnionedDecisions` on the decision `*l`. -/
theorem ConditionsAwareDecision.wp_ptr_UnionedDecisions_of
    (wp_X : ConditionsAwareDecision.UnionedDecisions.spec (GF := GF) (hG := hG))
    (l : Loc) (dl : DFrac) (d : ConditionsAwareDecision) (nds : List namedConditionsAwareDecision) :
    {{ l ↦{dl} d ∗ (d.union'.inner' ↦*□ nds : IProp GF) }}
      (App (Val (l @!! go.GoType.PointerType ConditionsAwareDecision.ty @!! go!"UnionedDecisions")) (Val #()))
    {{ (f : GoFunc), RET #f; l ↦{dl} d ∗
      seq2Ok (GF := GF) f (nds.map (fun nd => (nd.conditionalAuthorizerName', nd.d'))) }} := by
  iintro %Φ ⟨Hl, #Hs⟩ HΦ
  wp_method_call; (try wp_call)
  wp_auto
  iapply (wp_X d nds)
  · iexact Hs
  iintro !> %f Hf
  iapply HΦ
  iframe

end wps

end authorizer
end EtcdGrove
end Perennial
