/-
The proof of `Spec/fmt/ErrorfLeaf.lean`, from Perennial's `fmt.wp_Errorf` (fmtmodel, 2026-11-20;
until then over Perennial's previous model of `fmt.Errorf`, `errors.New(format)`, which ignored the
arguments).
-/
module

public import Spec.fmt.ErrorfLeaf
public import Perennial.Proof.fmt

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

/-- From Perennial's `fmt.wp_Errorf` (fmtmodel, 2026-11-20): its error (`fmt.errorfErr`) is an
`*errors.errorString`, a `*fmt.wrapError` or a `*fmt.wrapErrors`, with `Error() string`, no `Format`,
and an `Error()` returning the message; none of the three has an `Errors` method (goose's method
sets: `Error`; `Error`, `Unwrap`; `Error`, `Unwrap`). -/
theorem fmt.ErrorfLeaf.wp_proof :
    fmt.ErrorfLeaf.spec (GF := GF) (hG := hG) := by
  intro format args_sl xs dq
  iintro %Φ ⟨#Hpkg, Hsl, Hok⟩ HΦ
  wp_apply (_root_.Perennial.fmt.wp_Errorf format args_sl xs dq) $$ [$Hpkg $Hsl $Hok]
    as %err ⟨Hsl, %s, -, Herr⟩
  iunfold _root_.Perennial.fmt.errorfErr at Herr
  icases Herr with ⟨%hp, #HE, -⟩
  iapply HΦ
  iframe Hsl
  isplitr
  · unfold errOk
    isplitr
    · ipureintro; exact ⟨hp.2.1, hp.2.2.1⟩
    imodintro
    iintro %Ψ HΨ
    iapply HE
    inext
    iapply HΨ
  · ipureintro
    rcases hp.2.2.2 with h | h | h <;> rw [h]
    · have h := (go.MethodSetIs.method_set_is
        (t := go.GoType.PointerType errors.errorString.ty) go!"Errors")
      simpa [go.methodSetLookup] using h
    · have h := (go.MethodSetIs.method_set_is
        (t := go.GoType.PointerType _root_.Perennial.fmt.wrapError.ty) go!"Errors")
      simpa [go.methodSetLookup] using h
    · have h := (go.MethodSetIs.method_set_is
        (t := go.GoType.PointerType _root_.Perennial.fmt.wrapErrors.ty) go!"Errors")
      simpa [go.methodSetLookup] using h

end proof

end EtcdGrove
end Perennial
