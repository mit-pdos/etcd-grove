/-
`fmt.Errorf(format, args...)` with error arguments, and `errors.Is` on its result: `errors.Is(err, u)` returns for every
pointer target `u`, given the same of the wrapped argument. **A hypothesis** of `readWALNames`' and `openWALFiles`'
proofs until 2026-11-22, now proved (`Proof/fmt/ErrorfErrsTerm.lean`, from Perennial's `fmt.wp_Errorf`).

**Restated 2026-11-22** (ledger, "`fmt.ErrorfErrsNot.spec`/`fmt.ErrorfErrsTerm.spec` -- premises no proof can use";
the user's approval), as `fmt.ErrorfErrsNot.spec` (whose header says why): the error arguments' and the result's
facts are trees (`errTreeTerm`, `Spec/errors/ErrTree.lean`) instead of triples of `errors.Is` (`errIsTerm`, which
`errIsTerm_of_tree` gives); the format has at most one `%w` directive with an argument, one of the error arguments
(`fmt.wrapsAtMostOne`): the result is a leaf `*errors.errorString` or a `*fmt.wrapError` of it (two `%w`s, a
`*fmt.wrapErrors`, are left out: Perennial's `errorfErr` does not give its `errs` field).

The premise on the arguments is `fmt.ErrorfErrs.spec`'s (fmt soundness, 2026-11-18): `fmt.errArgsWf` with `errOk`
= `fmtErrorOk`; the post's `errOk err` is `fmtErrorOk` of the result. Ledger 2026-11-14, "no `errors.Is`
termination on their errors" (`wal-vsnap4`). Lean-first.
-/
module

public import Spec.fmt.ErrorfErrsNot

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The format wraps at most one argument, one of `errs`**: its directives parse, and its `%w` directives
with an argument (Go's `wrappedErrs`) are none, or one whose argument is one of `errs`. -/
def fmt.wrapsAtMostOne (format : GoString) (args : List GoInterface) (errs : List GoInterfaceOk) : Prop :=
  ∃ ds, _root_.Perennial.fmt.fmtDirectives format = some ds ∧
    (_root_.Perennial.fmt.wrapArgs ds args.length = [] ∨
      ∃ j e, _root_.Perennial.fmt.wrapArgs ds args.length = [j] ∧ args[j]? = some (GoInterface.ok e) ∧ e ∈ errs)

/-- See the file header. -/
abbrev fmt.ErrorfErrsTerm.spec : Prop :=
  ∀ (format : GoString) (args_sl : GoSlice) (args : List GoAny) (errs : List GoInterfaceOk),
  fmt.errArgsWf errs format args → fmt.wrapsAtMostOne format args errs →
    {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗ args_sl ↦* args ∗
        [∗list] e ∈ errs, errOk e ∗ errTreeTerm (GoInterface.ok e) }}
      (App (App (Val (@! _root_.Perennial.fmt.Errorf)) (Val #format)) (Val #args_sl))
    {{ (err : GoInterfaceOk), RET #(interface.ok err); errOk err ∗ errTreeTerm (GoInterface.ok err) }}

end spec

/-- **`fmt.wrapsAtMostOne` of a call with a literal format** (2026-11-22): the directives by `rfl`, then no `%w`, or
one whose argument is one of the error arguments. -/
macro "wraps_le1" : tactic => `(tactic| first
  | exact ⟨_, rfl, Or.inl rfl⟩
  | exact ⟨_, rfl, Or.inr ⟨_, _, rfl, rfl, by simp⟩⟩)

end EtcdGrove
end Perennial
