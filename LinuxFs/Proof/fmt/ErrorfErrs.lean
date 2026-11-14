/-
The proof of `LinuxFs/Spec/fmt/ErrorfErrs.lean`, over Perennial's model of `fmt.Errorf`
(`Perennial/TrustedCode/fmt.lean`: `errors.New(format)`, the arguments ignored), as Perennial's
`fmt.Errorf.wp_proof` is.

Why the model may be used here, although its spec (`fmt.Errorf.spec`) admits only basic arguments:
the model departs from Go by not calling the arguments' `Error()` methods while formatting. The
premise gives, of every error argument, that its `Error()` returns some string (`errOk`, a WP that
needs no resource), so Go's calls of them return without panicking, and Go's `Errorf` returns a
non-nil error whose `Error()` returns some string (a `*fmt.wrapError`/`*fmt.wrapErrors` or an
`*errors.errorString`): all the post says. The model's other departure (no wrapping) is invisible
to a post that says only `errOk`. (2026-11-14.)
-/
module

public import LinuxFs.Spec.fmt.ErrorfErrs
public import Perennial.Spec.errors.New

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [_root_.Perennial.fmt.Assumptions] [_root_.Perennial.errors.Assumptions]

theorem fmt.ErrorfErrs.wp_proof
    (wp_New : _root_.Perennial.errors.New.spec (GF := GF) (hG := hG)) :
    fmt.ErrorfErrs.spec (GF := GF) (hG := hG) := by
  intro format args_sl args errs _
  wp_start as _
  wp_apply wp_New as %err ⟨-, #Herr⟩
  iapply HΦ
  iunfold errOk
  imodintro
  iintro %Φ HΦ
  iapply Herr
  inext
  iapply HΦ

end proof

end EtcdGrove
end Perennial
