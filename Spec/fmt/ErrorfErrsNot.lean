/-
`fmt.Errorf(format, args...)` wrapping one error argument (`%w`), and what `errors.Is` answers on its result for a
pointer target `t` (`io.EOF`): **a hypothesis** of the WAL decoder's proofs until 2026-11-22, now proved
(`Proof/fmt/ErrorfErrsNot.lean`, from Perennial's `fmt.wp_Errorf` and the `*fmt.wrapError`'s `Unwrap`).

**Restated 2026-11-22** (ledger, "`fmt.ErrorfErrsNot.spec`/`fmt.ErrorfErrsTerm.spec` -- premises no proof can use";
the user's approval): until then the premises on the error arguments were `errIsNot e t`/`errIsTerm e`, triples
of `errors.Is(e, _)`, which no proof of `errors.Is` on the result can use (Go's `Is` walks the wrapped error's tree
itself, never calling `errors.Is` on it). They are now the trees Perennial's `errors.Is.spec` takes
(`errTreeNot`, `errTreeTerm`: `Spec/errors/ErrTree.lean`), and so is the post; `errIsNot_of_tree`/`errIsTerm_of_tree`
(`Proof/errors/ErrTree.lean`) give the old triples. The spec is narrowed to the WAL's calls: exactly one `%w`
directive, whose argument is one of the error arguments (`fmt.wrapsErr`), so the result is a `*fmt.wrapError` of
it; and a target that is no `*fmt.wrapError` (an `*errors.errorString` such as `io.EOF`), so the result is not the
target by its type. (With no `%w` the result is an `*errors.errorString` like `io.EOF`, and Perennial's
`errorfErr` gives no freshness of its pointer against the target's: that case is left out. With two, a
`*fmt.wrapErrors`, whose `errs` field `errorfErr` does not give.)

`errIsNot e t`/`errIsTerm e` (defined here, used by the WAL's specs and the trust boundary
`proto.UnmarshalWalRecordE`): `e` is not `t` and `errors.Is(e, t)` returns `false`; `errors.Is(e, u)` returns, for
every pointer target `u` (no answer claimed).

The premise on the arguments is `fmt.ErrorfErrs.spec`'s (fmt soundness, 2026-11-18): `fmt.errArgsWf` (an error
argument only under `%v`/`%s`/`%w`, no `#` in the format) with `errOk` = `fmtErrorOk` (`Error() string`, no
`Format`), so that Go calls only the error arguments' `Error()`; the post's `errOk err` is `fmtErrorOk` of the
result. W3a of `notes/wal-fsext-plan.md`; Lean-first.
-/
module

public import Spec.fmt.ErrorfErrs
public import Perennial.Proof.errors.Base
public import Spec.errors.ErrTree

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

/-- **`e` is not `t`, and `errors.Is(e, t)` answers `false`** (persistent). -/
def errIsNot (e t : GoInterface) : IProp GF :=
  iprop(⌜e ≠ t⌝ ∗ □ {{ (True : IProp GF) }}
      (App (App (Val (@! _root_.Perennial.errors.Is)) (Val #e)) (Val #t))
    {{ RET #false; True }})

instance errIsNot_persistent (e t : GoInterface) : Persistent (errIsNot (GF := GF) e t) := by
  unfold errIsNot; infer_instance

/-- **`errors.Is(e, u)` returns, for every pointer target `u`** (persistent; no answer claimed). -/
def errIsTerm (e : GoInterface) : IProp GF :=
  iprop(□ ∀ u : GoInterface, ⌜∀ tii, u = interface.ok tii → _root_.Perennial.errors.IsPointerError tii⌝ →
    {{ (True : IProp GF) }}
      (App (App (Val (@! _root_.Perennial.errors.Is)) (Val #e)) (Val #u))
    {{ (b : Bool), RET #b; True }})

instance errIsTerm_persistent (e : GoInterface) : Persistent (errIsTerm (GF := GF) e) := by
  unfold errIsTerm; infer_instance

/-- **The format wraps the error `e`**: its directives parse, exactly one `%w` has an argument (Go's
`wrappedErrs`), and that argument is `e`. -/
def fmt.wrapsErr (format : GoString) (args : List GoInterface) (e : GoInterfaceOk) : Prop :=
  ∃ ds j, _root_.Perennial.fmt.fmtDirectives format = some ds ∧
    _root_.Perennial.fmt.wrapArgs ds args.length = [j] ∧ args[j]? = some (GoInterface.ok e)

/-- See the file header. -/
abbrev fmt.ErrorfErrsNot.spec : Prop :=
  ∀ (format : GoString) (args_sl : GoSlice) (args : List GoAny) (errs : List GoInterfaceOk)
    (e : GoInterfaceOk) (t : GoInterface),
  fmt.errArgsWf errs format args → fmt.wrapsErr format args e → e ∈ errs →
  (∀ tii, t = interface.ok tii → _root_.Perennial.errors.IsPointerError tii ∧
    tii.ty ≠ go.GoType.PointerType _root_.Perennial.fmt.wrapError.ty) →
    {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗ args_sl ↦* args ∗
        ([∗list] e ∈ errs, errOk e) ∗ errTreeNot (GoInterface.ok e) t ∗ errTreeTerm (GoInterface.ok e) }}
      (App (App (Val (@! _root_.Perennial.fmt.Errorf)) (Val #format)) (Val #args_sl))
    {{ (err : GoInterfaceOk), RET #(interface.ok err); errOk err ∗ errTreeNot (GoInterface.ok err) t ∗
        errTreeTerm (GoInterface.ok err) }}

end spec

/-- **`fmt.wrapsErr` of a call with a literal format** (2026-11-22): the directives and the `%w` argument by `rfl`. -/
macro "wraps_err" : tactic => `(tactic| exact ⟨_, _, rfl, rfl, rfl⟩)

end EtcdGrove
end Perennial
