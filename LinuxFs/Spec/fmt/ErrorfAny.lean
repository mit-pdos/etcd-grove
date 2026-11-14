/-
`fmt.Errorf(format, args...)` with arguments of any type, **non-nil**: what `wal.Create`'s deferred
cleanup closure needs of `fmt.Errorf("%w (after: %v)", cerr, perr)` (S/wal.go, fork patch 0002:
`cleanupWAL`'s error wrapping the parent directory's), where nothing is known of the two errors
(`os`'s and the WAL's, whose `Error()` the callee specs do not give: `fmt.ErrorfErrs.spec` needs
`errOk` of each). Proved in `LinuxFs/Proof/fmt/ErrorfAny.lean` over Perennial's model of `Errorf`
(`errors.New(format)`, the arguments ignored), as `fmt.ErrorfErrs.wp_proof` is; **listed for review**
(plan §10). Why the model may be used for any arguments here: the post says only that the result is
not `nil`, which Go's `Errorf` always returns (a `*fmt.wrapError` with one `%w`, a `*fmt.wrapErrors`
with several, an `*errors.errorString` with none); Go's formatting calls the arguments' `Error()`
methods, and `fmt` recovers a panic in them (`printArg` -> `handleMethods`'s `defer p.catchPanic`,
which prints `%!v(PANIC=Error method: ...)`, and `<nil>` for a nil receiver), so the call does not panic
from them; a method that does not return makes the call not return (allowed by a partial-correctness
triple). What the model cannot represent, an argument's `Error()` with an effect on state the caller
owns, the errors here do not have: `os`'s `*PathError`/`*LinkError` and the WAL's errors build strings.
Lean-first.
-/
module

public import Perennial.Proof.fmt.Base

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
abbrev fmt.ErrorfAny.spec : Prop :=
  ∀ (format : GoString) (args_sl : GoSlice) (args : List GoAny) (dq : DFrac),
    {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗ args_sl ↦*{dq} args }}
      (App (App (Val (@! _root_.Perennial.fmt.Errorf)) (Val #format)) (Val #args_sl))
    {{ (err : GoInterface), RET #err; args_sl ↦*{dq} args ∗ ⌜err ≠ interface.nil⌝ }}

end spec

end EtcdGrove
end Perennial
