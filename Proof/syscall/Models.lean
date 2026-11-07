/-
The spec of the trusted model `syscall.arbitraryStrings` (`TrustedCode/syscall.lean`: an arbitrary
`[]string`, the model of the linknames `runtime_envs` and `os.runtime_args`), as Perennial's
`Proof/syscall/initialize.lean` (2026-11-07: this repository's `syscall`, project bboltfs's,
carries the same model).
-/
module

public import Code.syscall
public import Perennial.Proof.ProofPrelude
public import Perennial.Proof.fmt.SprintfModel

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The model `syscall.arbitraryStrings` returns some slice of strings (owned, with its
capacity). -/
theorem syscall.wp_arbitraryStrings :
    {{ (True : IProp GF) }}
      (App (Val syscall.arbitraryStrings) (Val #()))
    {{ (s : GoSlice), RET #s; ∃ xs : List GoString,
        s ↦* xs ∗ ownSliceCap GoString s (DFrac.own 1) }} := by
  iintro %Φ - HΦ
  unfold syscall.arbitraryStrings
  wp_auto
  -- `if arbitrary() != 0 { a = []string{} }`: then the loop, from either slice
  wp_apply wp_ArbitraryInt as %c0 -
  wp_if_destruct
  · ihave HI : (∃ (sl : GoSlice) (xs : List GoString),
        "a" ∷ a_ptr ↦ sl ∗ "Hsl" ∷ sl ↦* xs ∗
        "Hcap" ∷ ownSliceCap GoString sl (DFrac.own 1) : IProp GF) $$ [a]
    · iexists slice.nil, []
      iframe
      isplitl []
      · iapply ownSlice_nil
      · iapply ownSliceCap_nil

    wp_for HI
    wp_apply wp_ArbitraryInt as %c -
    wp_if_destruct
    · wp_apply fmt.wp_arbitraryString as %str -
      wp_apply wp_slice_literal (V := GoString) [str]
      isplitr
      · ipureintro; rfl
      iintro %sl2 ⟨Hsl2, -⟩
      wp_auto
      wp_apply wp_slice_append $$ [Hsl Hcap Hsl2] with %sl' ⟨Hsl, Hcap, -⟩
      · iframe
      wp_for_post
      iframe
      iexists _, _
      iframe
    · have Hf : (!decide (c = W64 0)) = false := by
        revert Hif; cases (!decide (c = W64 0)) <;> simp
      rw [Hf]
      simp only [_root_.decide_true, ↓reduceIte]
      wp_auto
      iapply HΦ
      iexists _
      iframe
  · wp_apply wp_slice_literal (V := GoString) []
    isplitr
    · ipureintro; rfl
    iintro %sl0 ⟨Hsl0, Hcap0⟩
    wp_auto
    ihave HI : (∃ (sl : GoSlice) (xs : List GoString),
        "a" ∷ a_ptr ↦ sl ∗ "Hsl" ∷ sl ↦* xs ∗
        "Hcap" ∷ ownSliceCap GoString sl (DFrac.own 1) : IProp GF) $$ [a Hsl0 Hcap0]
    · iexists _, []
      iframe

    wp_for HI
    wp_apply wp_ArbitraryInt as %c -
    wp_if_destruct
    · wp_apply fmt.wp_arbitraryString as %str -
      wp_apply wp_slice_literal (V := GoString) [str]
      isplitr
      · ipureintro; rfl
      iintro %sl2 ⟨Hsl2, -⟩
      wp_auto
      wp_apply wp_slice_append $$ [Hsl Hcap Hsl2] with %sl' ⟨Hsl, Hcap, -⟩
      · iframe
      wp_for_post
      iframe
      iexists _, _
      iframe
    · have Hf : (!decide (c = W64 0)) = false := by
        revert Hif; cases (!decide (c = W64 0)) <;> simp
      rw [Hf]
      simp only [_root_.decide_true, ↓reduceIte]
      wp_auto
      iapply HΦ
      iexists _
      iframe

end proof

end Perennial
