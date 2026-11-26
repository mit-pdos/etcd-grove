/-
What `errors.Is` needs of a context's error (`context.isCtxErr`): a leaf error without an `Is`
method, of a comparable type, `Canceled`'s `*errorString` (a pointer) or `DeadlineExceeded`'s
`deadlineExceededError{}` (a field-less struct, whose `==` is `true`: `ComparableErr` at the
target, perennial#677). Lean-first (errors-is-axioms, 2026-11-22), for `Proof/errors/IsCtxErr.lean`.

And (errors-is-deadline, 2026-11-23, for `Proof/errors/IsDeadlineExceeded.lean`) what Go's typing
gives of the errors of a tree compared with `context.DeadlineExceeded`, which the model, with no
typing of interface values, does not: those of type `deadlineExceededError` hold
`deadlineExceededError{}` (`deTypedErr`, `deTyped`).
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

section typing
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext] [GoLocalContext]
variable [sem : go.Semantics]

/-- An error of dynamic type `deadlineExceededError` holds `deadlineExceededError{}`. Go guarantees
this by typing (the type's only value). The model has no typing of interface values, so it is
stated. -/
def deTypedErr (ii : GoInterfaceOk) : Prop :=
  ii.ty = _root_.Perennial.context.deadlineExceededError.ty →
    ii.v = #(zero_val _root_.Perennial.context.deadlineExceededError)

/-- Every error of the tree `S` of type `deadlineExceededError` holds `deadlineExceededError{}`
(`deTypedErr`): what Go's `==` with the target `context.DeadlineExceeded` needs
(`deadlineExceededError_comparable`). -/
def deTyped (S : GoError → Prop) : Prop :=
  ∀ ii : GoInterfaceOk, S (interface.ok ii) → deTypedErr ii

/-- An error of a type other than `deadlineExceededError` (a pointer error, say) meets `deTypedErr`
vacuously. -/
theorem deTypedErr_of_ty (ii : GoInterfaceOk)
    (h : ii.ty ≠ _root_.Perennial.context.deadlineExceededError.ty) : deTypedErr ii :=
  fun h' => absurd h' h

/-- A pointer error meets `deTypedErr`. -/
theorem deTypedErr_ptr (ii : GoInterfaceOk) (h : _root_.Perennial.errors.IsPointerError ii) :
    deTypedErr ii := by
  obtain ⟨T, l, hT, -⟩ := h
  apply deTypedErr_of_ty
  rw [hT]
  unfold _root_.Perennial.context.deadlineExceededError.ty
  nofun

/-- `deadlineExceededError{}` itself meets `deTypedErr`. -/
theorem deTypedErr_zero :
    deTypedErr ⟨_root_.Perennial.context.deadlineExceededError.ty,
      #(zero_val _root_.Perennial.context.deadlineExceededError)⟩ :=
  fun _ => rfl

/-- A one-error tree is `deTyped` if its error is `deTypedErr`. -/
theorem deTyped_single (ii : GoInterfaceOk) (h : deTypedErr ii) :
    deTyped (· = interface.ok ii) := by
  intro ii' hS
  cases hS
  exact h

end typing

section value
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [ctx_sem : _root_.Perennial.context.Assumptions]

open Iris.ProofMode in
/-- `context.DeadlineExceeded` holds `deadlineExceededError{}` once `context` is initialized
(`isInit`'s `"#HDeadlineExceededTy"`; at any `HasLC`, unlike `context.isCtxErr_of_DeadlineExceeded`). -/
theorem deadlineExceeded_value (e : GoInterface) :
    isPkgInit (PROP := IProp GF) pkg_id.context ⊢
      globalAddr _root_.Perennial.context.DeadlineExceeded ↦□ e -∗
      ⌜e = interface.mkOk _root_.Perennial.context.deadlineExceededError.ty
        #(zero_val _root_.Perennial.context.deadlineExceededError)⌝ := by
  iintro #Hpkg #He
  ihave #Hi : (_root_.Perennial.context.isInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hi with ⟨-, -, -, -, -, -, #Hdv, -⟩
  icombine He Hdv gives %h
  ipureintro; exact h

open Iris.ProofMode in
/-- `context.DeadlineExceeded`'s value meets `deTypedErr`. -/
theorem deadlineExceeded_deTypedErr (ii : GoInterfaceOk) :
    isPkgInit (PROP := IProp GF) pkg_id.context ⊢
      globalAddr _root_.Perennial.context.DeadlineExceeded ↦□ GoInterface.ok ii -∗
      ⌜deTypedErr ii⌝ := by
  iintro #Hpkg #He
  ihave %h := deadlineExceeded_value _ $$ Hpkg He
  ipureintro
  cases h
  exact deTypedErr_zero

end value

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
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
    _root_.Perennial.errors.ComparableErr (GF := GF) S
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
    haveI : ⟦GoOp GoEquals _root_.Perennial.context.deadlineExceededError.ty, (#v1, #v2)⟧ ⤳ #true := by
      infer_instance
    exact _root_.Perennial.errors.pureWp_goEquals_of_step _ _ _ _

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

/-- A context's error meets `deTypedErr`: `Canceled`'s is a pointer, and `DeadlineExceeded`'s is
`deadlineExceededError{}`. -/
theorem isCtxErr_deTypedErr (ii : GoInterfaceOk) :
    context.isCtxErr (GF := GF) (GoInterface.ok ii) ⊢ ⌜deTypedErr ii⌝ := by
  iintro #He
  ihave %Hs := isCtxErr_shape (GoInterface.ok ii) $$ He
  ipureintro
  obtain ⟨ii', h, -, -, hp | rfl⟩ := Hs
  · cases h; exact deTypedErr_ptr ii hp
  · cases h; exact deTypedErr_zero

end shape

section noMatch
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **An error that `errors.Is(err, target)` does not match** (persistent; nonleaf-status-errs,
2026-11-26, shared by `notCtxTree` and `leasehttp.notLeaseNotFound`): `err` is in an error tree at
`target` (`errors.errorIsTree`: the specs of its errors' `Is` and `Unwrap` methods), with the typing
`P` the `Is` spec at `target` asks of the tree (`TreeTyped · target` for a pointer target, `deTyped`
for `context.DeadlineExceeded`), in which no error is `target` and no `Is` method may answer `true`
(`M`). Then `errors.Is(err, target)` answers `false` (the `Is` specs' posts). -/
def errors.noMatchTree (P : (GoError → Prop) → Prop) (err target : GoInterface) : IProp GF :=
  iprop(∃ (S : GoInterface → Prop) (M : GoInterfaceOk → Prop),
    _root_.Perennial.errors.errorIsTree (GF := GF) S M target ∗
    ⌜S err ∧ P S ∧ ∀ ii, S (GoInterface.ok ii) → GoInterface.ok ii ≠ target ∧ ¬ M ii⌝)

instance errors.noMatchTree_persistent (P : (GoError → Prop) → Prop) (err target : GoInterface) :
    Persistent (errors.noMatchTree (GF := GF) P err target) := by
  unfold errors.noMatchTree; infer_instance

end noMatch

end EtcdGrove
end Perennial
