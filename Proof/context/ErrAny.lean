/-
A context's `Err()` is `nil` until it is done, then `context.Canceled` or `context.DeadlineExceeded`
(`Spec/context/ErrAny.lean`): proved from Perennial's `isContext`, whose `Err` gives `isCtxErr` of a
non-nil error (an axiom until 2026-11-07; axiom sweep B2-4, `notes/axiom-review/sweep-plan-review.md`).
-/
module

public import Spec.context.ErrAny

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : context.Assumptions]

omit [GooseSemantics] [GooseInterp] in
/-- `deadlineExceededError` is no `*errorString` (distinct type constructors). -/
theorem deadlineExceededError_ty_ne_errorString_ptr :
    context.deadlineExceededError.ty ≠
      go.GoType.PointerType _root_.Perennial.errors.errorString.ty := by
  unfold context.deadlineExceededError.ty; simp

/-- What `ErrAny`'s postcondition says of a non-nil error, from `isCtxErr`. -/
theorem isCtxErr_ErrAny (err : GoInterface) :
    context.isCtxErr (GF := GF) err ⊢
      ⌜context.isTypedErr err⌝ ∗
        ((globalAddr context.Canceled ↦□ err ∗ ∃ x : Loc,
            ⌜err = interface.mkOk
              (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #x⌝ ∗
            x.[_root_.Perennial.errors.errorString, go!"s"] ↦□ go!"context canceled") ∨
          (globalAddr context.DeadlineExceeded ↦□ err ∗ ⌜∀ ii : GoInterfaceOk, err = .ok ii →
              ii.ty ≠ go.GoType.PointerType _root_.Perennial.errors.errorString.ty⌝)) := by
  iintro #He
  ihave %Ht := context.isCtxErr_typed err $$ He
  isplitr
  · ipureintro; exact Ht
  unfold context.isCtxErr
  icases He with (#Hc | ⟨#Hd, %hv⟩)
  · ileft; iexact Hc
  · iright; iframe Hd; ipureintro
    intro ii hii
    subst hv
    cases hii
    exact deadlineExceededError_ty_ne_errorString_ptr

/-- **`ctx.Err()`, from `isContext`** (no longer a trust boundary, 2026-11-07, axiom sweep B2-4):
`isContext`'s `"#HErr"` gives `isCtxErr` of a non-nil error, which is the postcondition's
disjunction (`isCtxErr_ErrAny`). -/
theorem context.ErrAny.wp_proof : context.ErrAny.spec (GF := GF) (hG := hG) := by
  intro c cd cl
  iintro %Φ ⟨#Hp, #Hc, Hcl⟩ HΦ
  unfold context.isContext context.isContextDef
  icases Hc with ⟨-, -, #HErr, -⟩
  iapply HErr $$ %cl [Hcl]
  · iexact Hcl
  inext
  iintro %err Hcase Hce
  iapply HΦ
  by_cases hn : err = interface.nil
  · subst hn
    iclear Hce
    isplitl [Hcase]
    · cases cl <;> simp only <;> try iexact Hcase
      all_goals (simp only [ite_true]; itrivial)
    · ileft; ipureintro; rfl
  · simp only [hn, ite_false]
    icases Hce with #Hce
    isplitl [Hcase]
    · cases cl
      all_goals simp only [hn] at *
      all_goals first | iexact Hcase | (icases Hcase with ⟨-, Hcl⟩; iexact Hcl)
    · iright
      iapply isCtxErr_ErrAny err $$ Hce

end proof

end EtcdGrove
end Perennial
