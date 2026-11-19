/-
Lean-first (no Rocq counterpart).

The `*ConditionEvaluationResult` method set's wrappers of `ConditionEvaluationResult`'s value
methods (Go calls `evalResult.IsTrue()` on the addressable local `evalResult` through them), from
the value methods' specs (hypotheses), as `PtrMethods.lean` does for `ConditionsAwareDecision`. For
`conditionsToAppliedErroredUnevaluated` and `partiallyEvaluateConditionsMapInternal`.
-/
module

public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionEvaluationResult__IsTrue
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionEvaluationResult__IsFalse
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionEvaluationResult__IsUnevaluatable
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionEvaluationResult__IsError
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionEvaluationResult__Error

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

/-- `(*ConditionEvaluationResult).IsTrue` on `*l`. -/
theorem ConditionEvaluationResult.wp_ptr_IsTrue_of
    (wp_IsTrue : ConditionEvaluationResult.IsTrue.spec (GF := GF) (hG := hG))
    (l : Loc) (dl : DFrac) (r : ConditionEvaluationResult) :
    {{ (l ↦{dl} r : IProp GF) }}
      (App (Val (l @!! go.GoType.PointerType ConditionEvaluationResult.ty @!! go!"IsTrue")) (Val #()))
    {{ RET #(decide (r.resultType' = W64 1)); l ↦{dl} r }} := by
  wp_start as Hl
  wp_auto
  wp_apply (wp_IsTrue r)
  iapply HΦ; iframe

/-- `(*ConditionEvaluationResult).IsFalse` on `*l`. -/
theorem ConditionEvaluationResult.wp_ptr_IsFalse_of
    (wp_IsFalse : ConditionEvaluationResult.IsFalse.spec (GF := GF) (hG := hG))
    (l : Loc) (dl : DFrac) (r : ConditionEvaluationResult) :
    {{ (l ↦{dl} r : IProp GF) }}
      (App (Val (l @!! go.GoType.PointerType ConditionEvaluationResult.ty @!! go!"IsFalse")) (Val #()))
    {{ RET #(decide (r.resultType' = W64 2)); l ↦{dl} r }} := by
  wp_start as Hl
  wp_auto
  wp_apply (wp_IsFalse r)
  iapply HΦ; iframe

/-- `(*ConditionEvaluationResult).IsUnevaluatable` on `*l`. -/
theorem ConditionEvaluationResult.wp_ptr_IsUnevaluatable_of
    (wp_IsUnevaluatable : ConditionEvaluationResult.IsUnevaluatable.spec (GF := GF) (hG := hG))
    (l : Loc) (dl : DFrac) (r : ConditionEvaluationResult) :
    {{ (l ↦{dl} r : IProp GF) }}
      (App (Val (l @!! go.GoType.PointerType ConditionEvaluationResult.ty @!! go!"IsUnevaluatable"))
        (Val #()))
    {{ RET #(decide (r.resultType' = W64 0)); l ↦{dl} r }} := by
  wp_start as Hl
  wp_auto
  wp_apply (wp_IsUnevaluatable r)
  iapply HΦ; iframe

/-- `(*ConditionEvaluationResult).IsError` on `*l`. -/
theorem ConditionEvaluationResult.wp_ptr_IsError_of
    (wp_IsError : ConditionEvaluationResult.IsError.spec (GF := GF) (hG := hG))
    (l : Loc) (dl : DFrac) (r : ConditionEvaluationResult) :
    {{ (l ↦{dl} r : IProp GF) }}
      (App (Val (l @!! go.GoType.PointerType ConditionEvaluationResult.ty @!! go!"IsError")) (Val #()))
    {{ RET #(decide (r.resultType' = W64 3)); l ↦{dl} r }} := by
  wp_start as Hl
  wp_auto
  wp_apply (wp_IsError r)
  iapply HΦ; iframe

/-- `(*ConditionEvaluationResult).Error` on `*l`. -/
theorem ConditionEvaluationResult.wp_ptr_Error_of
    (wp_Error : ConditionEvaluationResult.Error.spec (GF := GF) (hG := hG))
    (l : Loc) (dl : DFrac) (r : ConditionEvaluationResult) :
    {{ (l ↦{dl} r : IProp GF) }}
      (App (Val (l @!! go.GoType.PointerType ConditionEvaluationResult.ty @!! go!"Error")) (Val #()))
    {{ RET #(r.err'); l ↦{dl} r }} := by
  wp_start as Hl
  wp_auto
  wp_apply (wp_Error r)
  iapply HΦ; iframe

/-! Unfolding the untrusted-code predicates of `Defs.lean` one hypothesis at a time (an `unfold`
would reach every hypothesis and goal mentioning them). -/

theorem isCondition_elim (c : GoInterface) :
    isCondition (GF := GF) c ⊢ ∃ ci : GoInterfaceOk, ⌜c = .ok ci⌝ ∗
      strMethodOk ci go!"GetID" ∗ strMethodOk ci go!"GetType" ∗
      strMethodOk ci go!"GetCondition" ∗ strMethodOk ci go!"GetDescription" ∗
      (∀ (ctx data : GoInterface), condEvalOk ci ctx data) := by
  unfold isCondition; exact .rfl

theorem strMethodOk_elim (ci : GoInterfaceOk) (meth : GoString) :
    strMethodOk (GF := GF) ci meth ⊢
      {{ (True : IProp GF) }} (App (Val #(methods ci.ty meth ci.v)) (Val #()))
        {{ (s : GoString), RET #s; True }} := by
  unfold strMethodOk; exact .rfl

theorem evalCondOk_elim (ev : GoFunc) (cond : GoInterface) :
    evalCondOk (GF := GF) ev ⊢
      {{ isCondition (GF := GF) cond }} (App (Val #ev) (Val #cond))
        {{ (r : ConditionEvaluationResult), RET #r; True }} := by
  unfold evalCondOk evalCondCallOk
  iintro #H
  iexact H

/-- The conditions of the three lists of a conditions map, split. -/
theorem conds_app (l₁ l₂ : List GoInterface) :
    ([∗list] c ∈ l₁ ++ l₂, isCondition (GF := GF) c) ⊢
      ([∗list] c ∈ l₁, isCondition (GF := GF) c) ∗ ([∗list] c ∈ l₂, isCondition (GF := GF) c) :=
  BigSepL.bigSepL_append.1

/-- The two lists' conditions, joined. -/
theorem conds_app_intro (l₁ l₂ : List GoInterface) :
    ([∗list] c ∈ l₁, isCondition (GF := GF) c) ∗ ([∗list] c ∈ l₂, isCondition (GF := GF) c) ⊢
      ([∗list] c ∈ l₁ ++ l₂, isCondition (GF := GF) c) :=
  BigSepL.bigSepL_append.2

end wps

end authorizer
end EtcdGrove
end Perennial
