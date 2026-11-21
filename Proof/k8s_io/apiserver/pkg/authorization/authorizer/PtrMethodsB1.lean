/-
Lean-first (no Rocq counterpart).

More wrappers of `ConditionsAwareDecision`'s value methods in the `*ConditionsAwareDecision` method
set, as `PtrMethods.lean` (`IsDeny`, `IsNoOpinion`, `IsConditionsMap`, `IsUnion`, `ConditionsMap`, `Reason`, `Error`;
`Decision.String`), for the proofs of batch 1.
-/
module

public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__IsDeny
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__IsNoOpinion
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__IsConditionsMap
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__IsUnion
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__ConditionsMap
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__Reason
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__Error
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.Decision__String

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

/-- `(*ConditionsAwareDecision).Reason` on the decision `*l`. -/
theorem ConditionsAwareDecision.wp_ptr_Reason_of
    (wp_Reason : ConditionsAwareDecision.Reason.spec (GF := GF) (hG := hG))
    (l : Loc) (dl : DFrac) (d : ConditionsAwareDecision) :
    {{ (l ↦{dl} d : IProp GF) }}
      (App (Val (l @!! go.GoType.PointerType ConditionsAwareDecision.ty @!! go!"Reason"))
        (Val #()))
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
      (App (Val (l @!! go.GoType.PointerType ConditionsAwareDecision.ty @!! go!"Error"))
        (Val #()))
    {{ RET #(d.err'); l ↦{dl} d }} := by
  wp_start as Hl
  wp_auto
  wp_apply (wp_Error d)
  iapply HΦ; iframe

/-- `int` is not an interface type (Perennial has the instance for the type constructors but not
for the predeclared named types): for method calls on a `Decision` (`type Decision int`). -/
instance b1_notInterface_int : go.NotInterface go.int := ⟨trivial⟩

/-- `(*Decision).String` on the decision word `*l`. -/
theorem Decision.wp_ptr_String_of
    (wp_String : Decision.String.spec (GF := GF) (hG := hG))
    (l : Loc) (dl : DFrac) (k : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.authorization.authorizer ∗
        l ↦{dl} k }}
      (App (Val (l @!! go.GoType.PointerType Decision.ty @!! go!"String")) (Val #()))
    {{ (s : GoString), RET #s; l ↦{dl} k }} := by
  iintro %Φ ⟨#Hpkg, Hl⟩ HΦ
  wp_method_call; (try wp_call)
  wp_auto
  wp_apply (wp_String k) as %s -
  iapply HΦ
  iframe

end wps

end authorizer
end EtcdGrove
end Perennial
