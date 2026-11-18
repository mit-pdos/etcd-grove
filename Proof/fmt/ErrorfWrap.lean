/-
The proof of `Spec/fmt/ErrorfWrap.lean` (`fmt.Errorf` of `pre ++ "%w"` over one error), over
Perennial's model of `fmt.Errorf` (`Perennial/TrustedCode/fmt.lean`: `errors.New(format)`); an axiom
until H0 (2026-11-18, `notes/perheap-scope.md` §5a).
-/
module

public import Spec.fmt.ErrorfWrap

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
variable [package_sem : _root_.Perennial.fmt.Assumptions]

/-- **`fmt.Errorf(pre ++ "%w", inner)`, proved from Perennial's model** (H0, 2026-11-18; an axiom
from errorf-wrap, 2026-11-06, until then). The model (`errors.New(format)`) returns a fresh
`*errors.errorString` holding `format = pre ++ "%w"`: the post's left disjunct (`fmt.modelErrIs`,
with its cell). The description conjunct is conditional on an `Unwrap() error` method, which the
model's `*errors.errorString` does not have (its method set is `[Error]`, goose's generated
`errorString.TypeAssumptions`), so it holds vacuously here.

Why stepping into the model is sound for this statement, although the model does not model `%w`
(the review behind `etc/errorf-wrap-check.py`'s entry): the statement is true of Go's `Errorf` too.
Go's `Errorf` (`fmt/errors.go:34-81`) formats `pre ++ "%w"` (`pre` copied verbatim, having no `%`;
`%w` as `%v` of `inner`, calling its `Error()`, which returns by the premise) and, with exactly one
`%w` of a non-nil error operand, returns `&wrapError{msg: s, err: inner}`, whose methods are
`Error()` (`return e.msg`) and `Unwrap()` (`return e.err`): the right disjunct
(`fmt.wrapErrIs`); a `*wrapError` has `Unwrap() error` and no `GRPCStatus`, so its description is
its `Error()`, `pre ++ inner.Error()` (grpc `status/status.go:96-127`): the conditional conjunct.
Only reads the arguments' slice (`a[i].(error)` copies the value). Checked in Go:
`notes/axiom-review/errorf-wrap.md`. -/
theorem fmt.ErrorfWrap.wp_proof : fmt.ErrorfWrap.spec (GF := GF) (hG := hG) := by
  intro pre args_sl inner dq _
  wp_start as ⟨Hargs, -⟩
  wp_apply wp_New_errorString_cell as %x ⟨#Herr, #Hcell⟩
  iapply HΦ $$ %(⟨go.GoType.PointerType _root_.Perennial.errors.errorString.ty, #x⟩ : GoInterfaceOk)
  iframe Hargs
  isplitl
  · iunfold fmt.errorfWrapIs
    ileft
    iunfold fmt.modelErrIs
    iexists x
    isplitr
    · ipureintro; rfl
    iexists go!"%w"
    iframe Hcell
    iexact Herr
  · ipureintro
    intro h
    exfalso
    have hn : methodSet (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) !!
        go!"Unwrap" = none := by
      have := (go.method_set_is (t := go.GoType.PointerType _root_.Perennial.errors.errorString.ty)
        go!"Unwrap")
      simpa [go.methodSetLookup] using this
    simp only at h
    rw [hn] at h
    cases h

end proof

end EtcdGrove
end Perennial
