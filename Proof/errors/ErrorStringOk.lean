/-
An `errors.New` error is `fmtErrorOk` (`errorString_fmtErrorOk`): its dynamic type `*errorString`
has `Error() string` and no `Format` (the method set goose emits, in `errors.Assumptions`), and
`errors.wp_New_errorString`'s method spec is `fmt.stringMethodSpec`'s. Moved here from bbolt's
`Mmap/MmapSize` (2026-11-04, batch 30) so that bbolt's generated `errors/Init.lean` can give its
error variables' `fmtErrorOk` (`bboltErrorsVars`).
-/
module

public import Spec.fmt.ErrorOk
public import Perennial.Proof.errors

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section errs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [errors_sem : _root_.Perennial.errors.Assumptions]

/-- An `errors.New` error (`errors.wp_New_errorString`'s post) is `fmtErrorOk`. -/
theorem errorString_fmtErrorOk (x : Loc) (msg : GoString) :
    (□ ∀ Φ : val → IProp GF, ▷ Φ #msg -∗
      WP (App (Val #(methods (go.GoType.PointerType errors.errorString.ty) go!"Error" #x))
        (Val #())) {{ Φ }}) ⊢
    fmtErrorOk (interface.mkOk (go.GoType.PointerType errors.errorString.ty) #x) := by
  iintro #H
  simp only [fmtErrorOk, fmt.stringMethodSpec]
  isplitr
  · ipureintro
    have h1 := (go.MethodSetIs.method_set_is
      (t := go.GoType.PointerType errors.errorString.ty) go!"Format")
    have h2 := (go.MethodSetIs.method_set_is
      (t := go.GoType.PointerType errors.errorString.ty) go!"Error")
    simp only [go.methodSetLookup] at h1 h2
    exact ⟨by simpa using h1, by simpa [noArgStringSig] using h2⟩
  imodintro
  iintro %Φ HΦ
  iapply H
  inext
  iapply HΦ

end errs

end EtcdGrove
end Perennial
