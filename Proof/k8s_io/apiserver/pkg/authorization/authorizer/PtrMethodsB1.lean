/-
Lean-first (no Rocq counterpart).

More wrappers of `ConditionsAwareDecision`'s value methods in the `*ConditionsAwareDecision` method
set, as `PtrMethods.lean` (`IsDeny`, `IsNoOpinion`, `IsConditionsMap`, `IsUnion`, `ConditionsMap`), for the proofs of batch 1.
-/
module

public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__IsDeny
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__IsNoOpinion
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__IsConditionsMap
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__IsUnion
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__ConditionsMap

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

/-- `(*ConditionsAwareDecision).IsConditionsMap` on the decision `*l`. -/
theorem ConditionsAwareDecision.wp_ptr_IsConditionsMap_of
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

/-- `(*ConditionsAwareDecision).IsUnion` on the decision `*l`. -/
theorem ConditionsAwareDecision.wp_ptr_IsUnion_of
    (wp_IsUnion : ConditionsAwareDecision.IsUnion.spec (GF := GF) (hG := hG))
    (l : Loc) (dl : DFrac) (d : ConditionsAwareDecision) :
    {{ (l ↦{dl} d : IProp GF) }}
      (App (Val (l @!! go.GoType.PointerType ConditionsAwareDecision.ty @!! go!"IsUnion"))
        (Val #()))
    {{ RET #(decide (d.decisionType' = W64 14)); l ↦{dl} d }} := by
  wp_start as Hl
  wp_auto
  wp_apply (wp_IsUnion d)
  iapply HΦ; iframe

/-- `(*ConditionsAwareDecision).ConditionsMap` on the decision `*l`. -/
theorem ConditionsAwareDecision.wp_ptr_ConditionsMap_of
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

end wps

end authorizer
end EtcdGrove
end Perennial
