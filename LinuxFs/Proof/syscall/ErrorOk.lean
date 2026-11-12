/-
A nonzero errno's error is one Go's `fmt` formats by its `Error()` (`fmtErrorOk`,
`Spec/fmt/ErrorOk.lean`): `syscall.Errno`'s method set has `Error() string` and no `Format`
(goose's `Errno.TypeAssumptions`), and its `Error()` (trusted, `TrustedCode/syscall.lean`:
`fmt.arbitraryString`) returns some string, needing nothing. Used by the specs of `syscall`'s,
`golang.org/x/sys/unix`'s and `os`'s models, whose errors are `errnoErr e` (or a `*PathError`
wrapping one, `Proof/os/ErrorOk.lean`).
-/
module

public import LinuxFs.Proof.syscall.Base
public import Spec.fmt.ErrorOk

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : syscall.Assumptions]

/-- `fmt.arbitraryString` returns some string (Perennial's `fmt.wp_arbitraryString`, proved
here without `fmt`'s package assumptions, which it does not need). -/
theorem wp_arbitraryString' :
    {{ (True : IProp GF) }}
      (App (Val _root_.Perennial.fmt.arbitraryString) (Val #()))
    {{ (s : GoString), RET #s; True }} := by
  iintro %Φ - HΦ
  unfold _root_.Perennial.fmt.arbitraryString
  wp_auto
  ihave IH : iprop(∃ str : GoString, "s" ∷ s_ptr ↦ str) $$ [s]
  · iexists _; iframe
  wp_for IH
  wp_apply wp_ArbitraryInt as %c -
  wp_if_destruct
  · wp_apply wp_ArbitraryInt as %b -
    wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.byte))))
      (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := w8) (t := go.byte) [W8 (uint.Z b)]
    wp_auto
    rw [show go.arrayLiteralSize
      [KeyedElement none (ElementExpression go.byte #(W8 (uint.Z b)))] = 1 from rfl]
    isplitl []
    · ipureintro; rfl
    iintro %sl_ptr ⟨Hsl, -⟩
    wp_apply wp_bytes_to_string $$ Hsl as -
    wp_for_post
    iframe
    iexists _
    iframe
  · have Hf : (!decide (c = W64 0)) = false := by
      revert Hif; cases (!decide (c = W64 0)) <;> simp
    rw [Hf]
    simp only [_root_.decide_true, ↓reduceIte]
    wp_auto
    iapply HΦ; itrivial

/-- `Errno(e).Error()` returns some string. -/
theorem errno_stringMethodSpec (e : w64) :
    ⊢ EtcdGrove.fmt.stringMethodSpec (GF := GF) ⟨syscall.Errno.ty, #e⟩ go!"Error" := by
  unfold EtcdGrove.fmt.stringMethodSpec
  imodintro
  iintro %Φ HΦ
  simp only [method_unfold]
  unfold syscall.Errno.Error.impl
  wp_auto
  wp_apply wp_arbitraryString' as %s -
  iapply HΦ

/-- **A nonzero errno's error is `fmtErrorOk`.** -/
theorem errnoErr_fmtErrorOk (e : w64) (he : e ≠ 0) :
    ⊢ EtcdGrove.fmtErrorOk (GF := GF) (errnoErr e) := by
  unfold errnoErr
  simp only [he, ↓reduceIte, interface.mkOk, EtcdGrove.fmtErrorOk]
  isplitr
  · ipureintro
    have h1 := (go.MethodSetIs.method_set_is (t := syscall.Errno.ty) go!"Format")
    have h2 := (go.MethodSetIs.method_set_is (t := syscall.Errno.ty) go!"Error")
    simp only [go.methodSetLookup] at h1 h2
    exact ⟨by simpa using h1, by simpa [EtcdGrove.noArgStringSig] using h2⟩
  · iapply errno_stringMethodSpec

end wps

end Perennial
