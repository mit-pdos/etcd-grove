/-
What `errors.Is` needs of a context's error (`context.isCtxErr`): a leaf error without an `Is`
method, of a comparable type, `Canceled`'s `*errorString` (a pointer) or `DeadlineExceeded`'s
`deadlineExceededError{}` (a field-less struct, whose `==` is `true`: `ComparableErr` at the
target, perennial#677). Lean-first (errors-is-axioms, 2026-11-22), for `Proof/errors/IsCtxErr.lean`.
-/
module

public import Perennial.Proof.context
public import Proof.errors.NewVar

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [ctx_sem : _root_.Perennial.context.Assumptions]

instance deadlineExceededError_decEq :
    DecidableEq _root_.Perennial.context.deadlineExceededError :=
  fun a b => isTrue (by cases a; cases b; rfl)

/-- `deadlineExceededError` is a leaf error without an `Is` method (its method set: `Error`,
`Temporary`, `Timeout`). -/
theorem deadlineExceededError_leaf (v : val) :
    _root_.Perennial.errors.isLeafError ⟨_root_.Perennial.context.deadlineExceededError.ty, v⟩ ∧
      methodSet _root_.Perennial.context.deadlineExceededError.ty !! go!"Is" ≠
        some (go.Signature [go.error] false [go.bool]) := by
  have h := fun m => go.method_set_is (t := _root_.Perennial.context.deadlineExceededError.ty) m
  have hAs := h go!"As"; have hU := h go!"Unwrap"; have hIs := h go!"Is"
  simp only [go.methodSetLookup_cons, go.methodSetLookup_nil, gooseReduceIteDecide] at hAs hU hIs
  exact ⟨by simp [_root_.Perennial.errors.isLeafError, hAs, hU], by simp [hIs]⟩

/-- A `deadlineExceededError{}` target is comparable with the errors of a tree whose errors of its
type hold its (only) value: a field-less struct, whose `==` is `true`. -/
theorem deadlineExceededError_comparable (S : GoError → Prop)
    (htyped : ∀ ii : GoInterfaceOk, S (interface.ok ii) →
      ii.ty = _root_.Perennial.context.deadlineExceededError.ty →
      ii.v = #(zero_val _root_.Perennial.context.deadlineExceededError)) :
    _root_.Perennial.errors.ComparableErr S
      ⟨_root_.Perennial.context.deadlineExceededError.ty,
        #(zero_val _root_.Perennial.context.deadlineExceededError)⟩ := by
  refine ⟨_root_.Perennial.context.deadlineExceededError, inferInstance,
    fun a b _ => by cases a; cases b; rfl, ?_, fun v1 v2 => ?_,
    ⟨_, rfl⟩, fun ii hS hty => ⟨_, htyped ii hS hty⟩⟩
  · show ⟦CheckComparable _root_.Perennial.context.deadlineExceededError.ty, #()⟧ ⤳ #()
    have hf : _root_.Perennial.context.deadlineExceededError.fields = [] := by
      unfold _root_.Perennial.context.deadlineExceededError.fields; rfl
    haveI : ⟦CheckComparable (go.StructType _root_.Perennial.context.deadlineExceededError.fields),
        #()⟧ ⤳[under] #() := by
      rw [hf]; infer_instance
    infer_instance
  · have hd : decide (v1 = v2) = true := decide_eq_true (by cases v1; cases v2; rfl)
    rw [hd]
    show ⟦GoOp GoEquals _root_.Perennial.context.deadlineExceededError.ty, (#v1, #v2)⟧ ⤳ #true
    infer_instance

end lemmas

section shape
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.errors.Assumptions]
variable [ctx_sem : _root_.Perennial.context.Assumptions]

/-- What a context's error is, as `errors.Is` needs it: a leaf error without an `Is` method, of a
comparable type (a pointer or `deadlineExceededError{}`). -/
theorem isCtxErr_shape (e : GoInterface) :
    context.isCtxErr (GF := GF) e ⊢ ⌜∃ ii, e = GoInterface.ok ii ∧
      _root_.Perennial.errors.isLeafError ii ∧
      methodSet ii.ty !! go!"Is" ≠ some (go.Signature [go.error] false [go.bool]) ∧
      (_root_.Perennial.errors.IsPointerError ii ∨
        ii = ⟨_root_.Perennial.context.deadlineExceededError.ty,
          #(zero_val _root_.Perennial.context.deadlineExceededError)⟩)⌝ := by
  iintro #He
  unfold context.isCtxErr
  icases He with (⟨-, %x, %hx, -⟩ | ⟨-, %hv⟩)
  · ipureintro
    obtain ⟨hp, hl, hi⟩ := errorString_leaf x
    exact ⟨_, hx, hl, hi, Or.inl hp⟩
  · ipureintro
    obtain ⟨hl, hi⟩ := deadlineExceededError_leaf (GF := GF)
      (#(zero_val _root_.Perennial.context.deadlineExceededError))
    exact ⟨_, hv, hl, hi, Or.inr rfl⟩

end shape

end EtcdGrove
end Perennial
