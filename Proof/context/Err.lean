/-
The error a context's `Err()` returns has an `Error()` that returns some string
(`Spec/context/Err.lean`): proved from Perennial's `isContext` (`isCtxErr`) and
`wp_isCtxErr_Error` (an axiom until 2026-11-07; axiom sweep B2-4). Lean-first (no Rocq
counterpart).
-/
module

public import Spec.context.Err
public import Perennial.Proof.context.NewErrorString

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

/-- **`ctx.Err()`'s error has a string `Error()`, from `isContext`** (no longer a trust boundary,
2026-11-07, axiom sweep B2-4): `"#HErr"` gives `isCtxErr` of a non-nil error, and Perennial's
`wp_isCtxErr_Error` its `Error()`. -/
theorem context.Err.wp_proof : context.Err.spec (GF := GF) (hG := hG) := by
  intro c s cl
  iintro #Hc
  unfold context.isContext context.isContextDef
  icases Hc with ⟨-, -, #HErr, -⟩
  imodintro
  iintro %Φ Hcl HΦ
  iapply HErr $$ %cl [Hcl]
  · iexact Hcl
  inext
  iintro %err Hcase Hce
  iapply HΦ $$ [Hcase]
  · iexact Hcase
  unfold context.errStringOk
  by_cases hn : err = interface.nil
  · subst hn
    imodintro
    iintro %e %he
    cases he
  simp only [hn, ite_false]
  icases Hce with #Hce
  imodintro
  iintro %e %he
  isplitl
  · unfold fmt.stringMethodSpec
    imodintro
    iintro %Ψ HΨ
    iapply context.wp_isCtxErr_Error err e he $$ Hce
    inext
    iintro %str -
    iapply HΨ
  · -- (premise-fixes-4) the two errors' types, from `isCtxErr`: no `Format`
    unfold context.isCtxErr
    icases Hce with (⟨-, %x, %hx, -⟩ | ⟨-, %hv⟩)
    · rw [hx] at he; cases he
      have h := go.method_set_is
        (t := go.GoType.PointerType _root_.Perennial.errors.errorString.ty) go!"Format"
      simp only [go.methodSetLookup_cons, go.methodSetLookup_nil, gooseReduceIteDecide] at h
      ipureintro; exact h
    · rw [hv] at he; cases he
      have h := go.method_set_is (t := context.deadlineExceededError.ty) go!"Format"
      simp only [go.methodSetLookup_cons, go.methodSetLookup_nil, gooseReduceIteDecide] at h
      ipureintro; exact h

end proof

end EtcdGrove
end Perennial
