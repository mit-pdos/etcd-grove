/-
The proof of `Spec/fmt/ErrorfErrs.lean`, over Perennial's model of `fmt.Errorf`
(`Perennial/TrustedCode/fmt.lean`: `errors.New(format)`, the arguments ignored), as Perennial's
`fmt.Errorf.wp_proof` is.

Why the model may be used here, although its spec (`fmt.Errorf.spec`) admits only basic arguments:
the model departs from Go by not calling the arguments' `Error()` methods while formatting. The
premise (`fmt.errArgsWf`, `errOk` = `fmtErrorOk`) gives that Go calls only those `Error()` methods
(no `Format`, no `%#v`, no reflection into an error's fields), each returning some string needing
nothing, so the call touches no caller-owned memory and does not panic; Go's `Errorf` returns a non-nil
`*fmt.wrapError`/`*fmt.wrapErrors`/`*errors.errorString` (`Error() string`, no `Format`): `errOk`,
all the post says, which the model's `*errorString` also is (`errorString_fmtErrorOk`, from
`errors.wp_New_errorString`'s exact type). The model's other departure (no wrapping) is invisible
to a post that says only `errOk`. (2026-11-14; premise and post restated 2026-11-18, fmt soundness.)
-/
module

public import Spec.fmt.ErrorfErrs
public import Perennial.Proof.errors.NewVar
public import Proof.errors.ErrorStringOk

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

theorem fmt.ErrorfErrs.wp_proof :
    fmt.ErrorfErrs.spec (GF := GF) (hG := hG) := by
  intro format args_sl args errs _
  wp_start as _
  wp_apply _root_.Perennial.errors.wp_New_errorString as %x #Herr
  iapply HΦ
  iapply errorString_errOk
  iexact Herr

end proof

end EtcdGrove
end Perennial
