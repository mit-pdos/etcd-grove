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
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsMap__DenyConditions
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsMap__NoOpinionConditions
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsMap__AllowConditions

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
theorem ConditionEvaluationResult.wp_ptr_IsTrue_of_b2
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
theorem ConditionEvaluationResult.wp_ptr_IsFalse_of_b2
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
theorem ConditionEvaluationResult.wp_ptr_IsUnevaluatable_of_b2
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
theorem ConditionEvaluationResult.wp_ptr_IsError_of_b2
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
theorem ConditionEvaluationResult.wp_ptr_Error_of_b2
    (wp_Error : ConditionEvaluationResult.Error.spec (GF := GF) (hG := hG))
    (l : Loc) (dl : DFrac) (r : ConditionEvaluationResult) :
    {{ (l ↦{dl} r : IProp GF) }}
      (App (Val (l @!! go.GoType.PointerType ConditionEvaluationResult.ty @!! go!"Error")) (Val #()))
    {{ RET #(r.err'); l ↦{dl} r }} := by
  wp_start as Hl
  wp_auto
  wp_apply (wp_Error r)
  iapply HΦ; iframe

/-- `(*ConditionsMap).DenyConditions` on `*l`. -/
theorem ConditionsMap.wp_ptr_DenyConditions_of_b2
    (wp_DenyConditions : ConditionsMap.DenyConditions.spec (GF := GF) (hG := hG))
    (l : Loc) (dl : DFrac) (c : ConditionsMap) (cs : List GoInterface) :
    {{ (l ↦{dl} c ∗ c.denyConditions' ↦*□ cs : IProp GF) }}
      (App (Val (l @!! go.GoType.PointerType ConditionsMap.ty @!! go!"DenyConditions")) (Val #()))
    {{ (f : GoFunc), RET #f; l ↦{dl} c ∗ seqOk (GF := GF) f cs }} := by
  wp_start as ⟨Hl, #Hcs⟩
  wp_auto
  wp_apply (wp_DenyConditions c cs) as %f Hf
  · iexact Hcs
  iapply HΦ; iframe

/-- `(*ConditionsMap).NoOpinionConditions` on `*l`. -/
theorem ConditionsMap.wp_ptr_NoOpinionConditions_of_b2
    (wp_NoOpinionConditions : ConditionsMap.NoOpinionConditions.spec (GF := GF) (hG := hG))
    (l : Loc) (dl : DFrac) (c : ConditionsMap) (cs : List GoInterface) :
    {{ (l ↦{dl} c ∗ c.noOpinionConditions' ↦*□ cs : IProp GF) }}
      (App (Val (l @!! go.GoType.PointerType ConditionsMap.ty @!! go!"NoOpinionConditions")) (Val #()))
    {{ (f : GoFunc), RET #f; l ↦{dl} c ∗ seqOk (GF := GF) f cs }} := by
  wp_start as ⟨Hl, #Hcs⟩
  wp_auto
  wp_apply (wp_NoOpinionConditions c cs) as %f Hf
  · iexact Hcs
  iapply HΦ; iframe

/-- `(*ConditionsMap).AllowConditions` on `*l`. -/
theorem ConditionsMap.wp_ptr_AllowConditions_of_b2
    (wp_AllowConditions : ConditionsMap.AllowConditions.spec (GF := GF) (hG := hG))
    (l : Loc) (dl : DFrac) (c : ConditionsMap) (cs : List GoInterface) :
    {{ (l ↦{dl} c ∗ c.allowConditions' ↦*□ cs : IProp GF) }}
      (App (Val (l @!! go.GoType.PointerType ConditionsMap.ty @!! go!"AllowConditions")) (Val #()))
    {{ (f : GoFunc), RET #f; l ↦{dl} c ∗ seqOk (GF := GF) f cs }} := by
  wp_start as ⟨Hl, #Hcs⟩
  wp_auto
  wp_apply (wp_AllowConditions c cs) as %f Hf
  · iexact Hcs
  iapply HΦ; iframe

/-! Unfolding the untrusted-code predicates of `Defs.lean` one hypothesis at a time (an `unfold`
would reach every hypothesis and goal mentioning them). -/

theorem isCondition_elim_b2 (c : GoInterface) :
    isCondition (GF := GF) c ⊢ ∃ ci : GoInterfaceOk, ⌜c = .ok ci⌝ ∗
      strMethodOk ci go!"GetID" ∗ strMethodOk ci go!"GetType" ∗
      strMethodOk ci go!"GetCondition" ∗ strMethodOk ci go!"GetDescription" ∗
      (∀ (ctx data : GoInterface), condEvalOk ci ctx data) := by
  unfold isCondition; exact .rfl

theorem strMethodOk_elim_b2 (ci : GoInterfaceOk) (meth : GoString) :
    strMethodOk (GF := GF) ci meth ⊢
      {{ (True : IProp GF) }} (App (Val #(methods ci.ty meth ci.v)) (Val #()))
        {{ (s : GoString), RET #s; True }} := by
  unfold strMethodOk; exact .rfl

theorem evalCondOk_elim_b2 (ev : GoFunc) (cond : GoInterface) :
    evalCondOk (GF := GF) ev ⊢
      {{ isCondition (GF := GF) cond }} (App (Val #ev) (Val #cond))
        {{ (r : ConditionEvaluationResult), RET #r; resOk r }} := by
  unfold evalCondOk evalCondCallOk
  iintro #H
  iexact H

/-- The conditions of the three lists of a conditions map, split. -/
theorem conds_app_b2 (l₁ l₂ : List GoInterface) :
    ([∗list] c ∈ l₁ ++ l₂, isCondition (GF := GF) c) ⊢
      ([∗list] c ∈ l₁, isCondition (GF := GF) c) ∗ ([∗list] c ∈ l₂, isCondition (GF := GF) c) :=
  BigSepL.bigSepL_append.1

/-- The two lists' conditions, joined. -/
theorem conds_app_intro_b2 (l₁ l₂ : List GoInterface) :
    ([∗list] c ∈ l₁, isCondition (GF := GF) c) ∗ ([∗list] c ∈ l₂, isCondition (GF := GF) c) ⊢
      ([∗list] c ∈ l₁ ++ l₂, isCondition (GF := GF) c) :=
  BigSepL.bigSepL_append.2

theorem condEvalOk_elim_b2 (ci : GoInterfaceOk) (ctx data : GoInterface) :
    condEvalOk (GF := GF) ci ctx data ⊢
      {{ (True : IProp GF) }}
        (App (App (Val #(methods ci.ty go!"Evaluate" ci.v)) (Val #ctx)) (Val #data))
        {{ (r : ConditionEvaluationResult), RET #r; resOk r }} := by
  unfold condEvalOk; exact .rfl

theorem maybeEvalCallOk_elim_b2 (f : GoFunc) (ctx cond data : GoInterface) :
    maybeEvalCallOk (GF := GF) f ctx cond data ⊢
      {{ isCondition (GF := GF) cond }}
        (App (App (App (Val #f) (Val #ctx)) (Val #cond)) (Val #data))
        {{ (r : ConditionEvaluationResult), RET #r; resOk r }} := by
  unfold maybeEvalCallOk; exact .rfl

theorem maybeEvalFnOk_elim_b2 (f : GoFunc) :
    maybeEvalFnOk (GF := GF) f ⊢
      ⌜f = func.nil⌝ ∨ ∀ (ctx cond data : GoInterface), maybeEvalCallOk f ctx cond data := by
  unfold maybeEvalFnOk; exact .rfl

theorem evalCallOk_elim_b2 (f : GoFunc) (ctx cond data : GoInterface) :
    evalCallOk (GF := GF) f ctx cond data ⊢
      {{ isCondition (GF := GF) cond }}
        (App (App (App (Val #f) (Val #ctx)) (Val #cond)) (Val #data))
        {{ (b : Bool) (e : GoInterface), RET (PairV #b #e); utilerrors.errTreeOrNil e }} := by
  unfold evalCallOk; exact .rfl

theorem evalFnOk_elim_b2 (f : GoFunc) (ctx cond data : GoInterface) :
    evalFnOk (GF := GF) f ⊢ evalCallOk f ctx cond data := by
  unfold evalFnOk
  iintro #H
  iexact H

/-- Names the value of a points-to (for a closure held in a local variable: its proof gets the
closure as an equation, the rest of the proof an abstract value). -/
theorem pointsto_name_b2 {V : Type} [TypedPointsto (GF := GF) V] (l : Loc) (v : V) :
    (l ↦ v : IProp GF) ⊢ ∃ w : V, l ↦ w ∗ ⌜w = v⌝ := by
  iintro H
  iexists v
  iframe
  ipureintro; rfl

end wps

end authorizer
end EtcdGrove
end Perennial
