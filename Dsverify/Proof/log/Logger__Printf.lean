/-
**Trust-boundary axiom** (dsv-fix4, mit-pdos/etcd-grove#49 fix 4): `l.Printf(format, args...)` on a
non-`nil` `*Logger`, with arguments `argOk` allows (`nil`, a value `fmt` formats without calling a
method of it, a value whose type has neither `Error` nor `String`, or an error whose `Error()`
returns, `models_lab.errAny`), returns and gives the argument slice back. Perennial's trusted model
of `log` does not translate `*Logger`'s methods (`Perennial/Code/log.toml`). Go's `log.go`:
`Printf` calls `l.output(0, 2, func(b) { return fmt.Appendf(b, format, v...) })`; `output` reads the
logger's atomic flags and prefix, formats under the logger's mutex into a pooled buffer and writes it
to the logger's `io.Writer` (the standard logger's `os.Stderr`), ignoring a write error; a `*Logger`
is safe for concurrent use, so the call needs no ownership of it. A nil `l` panics (excluded:
`l ≠ null`). `fmt` calls no method of an argument but `Error()` of an error (`%v`/`%s`, `argOk`'s
`errAny`), whatever the format string; it reads the argument slice only. The field `wp_Logger_Printf`
of craq's statement premise `LogHyp` until dsv-fix4 (`Dsverify/Proof/github_com/despreston/go_craq/
Craq/LogHyp.lean`). Review: `notes/axiom-review/dsv-fix4/log-logger.md`.
-/
module

public import Dsverify.Proof.github_com.despreston.go_craq.Craq.LogHyp

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.despreston.go_craq (argOk)

section ax
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [sem : go.Semantics]
variable [log.Assumptions]

/-- **Trust-boundary axiom** (the file header). -/
axiom log.Logger.Printf.wp_proof : ∀ (l : Loc) (msg : GoString) (arg : GoSlice)
    (xs : List GoInterface) (dq : DFrac), l ≠ null →
    {{ isPkgInit (PROP := IProp GF) pkg_id.log ∗ arg ↦*{dq} xs ∗ [∗list] x ∈ xs, argOk x }}
      (App (App (Val (l @!! go.GoType.PointerType log.Logger.ty @!! go!"Printf")) (Val #msg))
        (Val #arg))
    {{ RET #(); arg ↦*{dq} xs }}

end ax

end Perennial
