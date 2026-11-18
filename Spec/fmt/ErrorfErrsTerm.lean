/-
`fmt.Errorf(format, args...)` with error arguments, and `errors.Is` on its result: `fmt.ErrorfErrs.spec`, with
`errIsTerm` (`errors.Is(e, u)` returns for every pointer target `u`) passed from the error arguments to the
result. **A hypothesis** (of `readWALNames`' and `openWALFiles`' proofs), not proved here and not an axiom, as
`fmt.ErrorfErrs.spec` and `fmt.ErrorfErrsNot.spec` (whose `errIsTerm` part it is, without that spec's target
`t`): true of Go (the result is a fresh `*fmt.wrapError`/`*fmt.wrapErrors`/`*errors.errorString`, compared with
`u`, with no `Is` method, whose `Unwrap` gives the `%w` arguments, whose walks return) and of Perennial's model
(`errors.New(format)`, a leaf). The general fix is a Perennial change (`notes/perennial-changes.md`, 2026-11-14,
"`errors.Is` on `fmt.Errorf`'s result"). Ledger 2026-11-14, "no `errors.Is` termination on their errors"
(`wal-vsnap4`). Lean-first.

Restated 2026-11-18 (fmt soundness; approved by the user, 2026-11-18, via etcd-grove-03): the premise is
`fmt.ErrorfErrs.spec`'s, `fmt.errArgsWf` (an error argument only under `%v`/`%s`/`%w` without `#`) with
`errOk` = `fmtErrorOk` (`Error() string`, no `Format`), so that Go calls only the error arguments'
`Error()`; the post's `errOk err` says `fmtErrorOk` of the result (true of Go's three result types and of
the model's). Until then any verb and any type with an `Error()` WP were admitted, which Go does not satisfy
(`Format` methods, `Error() int`: `Spec/fmt/ErrorfErrs.lean`'s header).
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

/-- See the file header. -/
abbrev fmt.ErrorfErrsTerm.spec : Prop :=
  ∀ (format : GoString) (args_sl : GoSlice) (args : List GoAny) (errs : List GoInterfaceOk),
  fmt.errArgsWf errs format args →
    {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗ args_sl ↦* args ∗
        [∗list] e ∈ errs, errOk e ∗ errIsTerm (GoInterface.ok e) }}
      (App (App (Val (@! _root_.Perennial.fmt.Errorf)) (Val #format)) (Val #args_sl))
    {{ (err : GoInterfaceOk), RET #(interface.ok err); errOk err ∗ errIsTerm (GoInterface.ok err) }}

end spec

end EtcdGrove
end Perennial
