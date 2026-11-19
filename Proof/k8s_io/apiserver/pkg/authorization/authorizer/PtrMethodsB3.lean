/-
Lean-first (no Rocq counterpart).

More of the `*ConditionsAwareDecision` method set's wrappers of `ConditionsAwareDecision`'s value
methods (as `PtrMethods.lean`), for `collectReasonsAndErrors`, which holds its decision in a local
variable: `IsDeny`, `IsNoOpinion`, `IsUnion`, `Reason`, `Error`, `UnionedDecisions`.
-/
module

public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__IsDeny
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__IsNoOpinion
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__IsUnion
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__Reason
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__Error
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__UnionedDecisions

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

/-- `(*ConditionsAwareDecision).IsDeny` on the decision `*l`. -/
theorem ConditionsAwareDecision.wp_ptr_IsDeny_of
    (wp_IsDeny : ConditionsAwareDecision.IsDeny.spec (GF := GF) (hG := hG))
    (l : Loc) (dl : DFrac) (d : ConditionsAwareDecision) :
    {{ (l ↦{dl} d : IProp GF) }}
      (App (Val (l @!! go.GoType.PointerType ConditionsAwareDecision.ty @!! go!"IsDeny")) (Val #()))
    {{ RET #(decide (d.decisionType' = W64 0)); l ↦{dl} d }} := by
  wp_start as Hl
  wp_auto
  wp_apply (wp_IsDeny d)
  iapply HΦ; iframe

/-- `(*ConditionsAwareDecision).IsNoOpinion` on the decision `*l`. -/
theorem ConditionsAwareDecision.wp_ptr_IsNoOpinion_of
    (wp_IsNoOpinion : ConditionsAwareDecision.IsNoOpinion.spec (GF := GF) (hG := hG))
    (l : Loc) (dl : DFrac) (d : ConditionsAwareDecision) :
    {{ (l ↦{dl} d : IProp GF) }}
      (App (Val (l @!! go.GoType.PointerType ConditionsAwareDecision.ty @!! go!"IsNoOpinion"))
        (Val #()))
    {{ RET #(decide (d.decisionType' = W64 12)); l ↦{dl} d }} := by
  wp_start as Hl
  wp_auto
  wp_apply (wp_IsNoOpinion d)
  iapply HΦ; iframe

/-- `(*ConditionsAwareDecision).IsUnion` on the decision `*l`. -/
theorem ConditionsAwareDecision.wp_ptr_IsUnion_of
    (wp_IsUnion : ConditionsAwareDecision.IsUnion.spec (GF := GF) (hG := hG))
    (l : Loc) (dl : DFrac) (d : ConditionsAwareDecision) :
    {{ (l ↦{dl} d : IProp GF) }}
      (App (Val (l @!! go.GoType.PointerType ConditionsAwareDecision.ty @!! go!"IsUnion")) (Val #()))
    {{ RET #(decide (d.decisionType' = W64 14)); l ↦{dl} d }} := by
  wp_start as Hl
  wp_auto
  wp_apply (wp_IsUnion d)
  iapply HΦ; iframe

/-- `(*ConditionsAwareDecision).Reason` on the decision `*l`. -/
theorem ConditionsAwareDecision.wp_ptr_Reason_of
    (wp_Reason : ConditionsAwareDecision.Reason.spec (GF := GF) (hG := hG))
    (l : Loc) (dl : DFrac) (d : ConditionsAwareDecision) :
    {{ (l ↦{dl} d : IProp GF) }}
      (App (Val (l @!! go.GoType.PointerType ConditionsAwareDecision.ty @!! go!"Reason")) (Val #()))
    {{ RET #(d.reason'); l ↦{dl} d }} := by
  wp_start as Hl
  wp_auto
  wp_apply (wp_Reason d)
  iapply HΦ; iframe

/-- `(*ConditionsAwareDecision).Error` on the decision `*l`. -/
theorem ConditionsAwareDecision.wp_ptr_Error_of
    (wp_Error : ConditionsAwareDecision.Error.spec (GF := GF) (hG := hG))
    (l : Loc) (dl : DFrac) (d : ConditionsAwareDecision) :
    {{ (l ↦{dl} d : IProp GF) }}
      (App (Val (l @!! go.GoType.PointerType ConditionsAwareDecision.ty @!! go!"Error")) (Val #()))
    {{ RET #(d.err'); l ↦{dl} d }} := by
  wp_start as Hl
  wp_auto
  wp_apply (wp_Error d)
  iapply HΦ; iframe

/-- `(*ConditionsAwareDecision).UnionedDecisions` on the decision `*l`. -/
theorem ConditionsAwareDecision.wp_ptr_UnionedDecisions_of
    (wp_UnionedDecisions : ConditionsAwareDecision.UnionedDecisions.spec (GF := GF) (hG := hG))
    (l : Loc) (dl : DFrac) (d : ConditionsAwareDecision) (nds : List namedConditionsAwareDecision) :
    {{ (l ↦{dl} d ∗ d.union'.inner' ↦*□ nds : IProp GF) }}
      (App (Val (l @!! go.GoType.PointerType ConditionsAwareDecision.ty @!! go!"UnionedDecisions"))
        (Val #()))
    {{ (f : GoFunc), RET #f; l ↦{dl} d ∗
        seq2Ok (GF := GF) f (nds.map (fun nd => (nd.conditionalAuthorizerName', nd.d'))) }} := by
  wp_start as ⟨Hl, #Hs⟩
  wp_auto
  wp_apply (wp_UnionedDecisions d nds) as %f #Hf
  · iexact Hs
  iapply HΦ; iframe; iexact Hf

end wps

end authorizer
end EtcdGrove
end Perennial
