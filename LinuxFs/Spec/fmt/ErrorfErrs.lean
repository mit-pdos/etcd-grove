/-
`fmt.Errorf(format, args...)` with error arguments (`%w`): **a hypothesis** of the WAL decoder's
proofs, not proved here and not an axiom. Perennial's `fmt.Errorf.spec` requires every argument to
be of a basic type (`ArgsWf`): Go's `Errorf` calls the `Error()` method of an error argument, which
the model (`errors.New(format)`, ignoring the arguments) does not. The decoder wraps
`io.ErrUnexpectedEOF` and `Record.Validate`'s error (decoder.go:112, :147-149) and `Validate` wraps
`walpb.ErrCRCMismatch` (record.go:26-30): errors whose `Error()` returns a string (`errOk`). The
general fix is a Perennial change (an `Errorf` spec admitting error arguments whose `Error()` is
safe, `notes/perennial-changes.md`); the statement below is what it would give.

Note that the model does not wrap: `errors.Is(err, io.ErrUnexpectedEOF)` of the result is not what
Go answers. The decoder's specs therefore say only that such an error is not `nil`.
W3a of `notes/wal-fsext-plan.md`; Lean-first.
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

/-- An error whose `Error()` returns some string (persistent). -/
def errOk (e : GoInterfaceOk) : IProp GF :=
  iprop(□ ∀ Φ : val → IProp GF, ▷ (∀ str : GoString, Φ #str) -∗
    WP (App (Val #(methods e.ty go!"Error" e.v)) (Val #())) {{ Φ }})

instance errOk_persistent (e : GoInterfaceOk) : Persistent (errOk (GF := GF) e) := by
  unfold errOk; infer_instance

/-- See the file header. -/
abbrev fmt.ErrorfErrs.spec : Prop :=
  ∀ (format : GoString) (args_sl : GoSlice) (args : List GoAny) (errs : List GoInterfaceOk),
  (∀ ii, interface.ok ii ∈ args → fmt.ArgWf ii ∨ ii ∈ errs) →
    {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗ args_sl ↦* args ∗ [∗list] e ∈ errs, errOk e }}
      (App (App (Val (@! _root_.Perennial.fmt.Errorf)) (Val #format)) (Val #args_sl))
    {{ (err : GoInterfaceOk), RET #(interface.ok err); errOk err }}

end spec

end EtcdGrove
end Perennial
