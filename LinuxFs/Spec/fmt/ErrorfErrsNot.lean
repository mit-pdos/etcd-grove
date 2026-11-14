/-
`fmt.Errorf(format, args...)` with error arguments, and what `errors.Is` answers on its result for a
target `t` held by a package variable (`io.EOF`): **a hypothesis** of the WAL decoder's proofs (as
`fmt.ErrorfErrs.spec`, whose post it extends), not proved here and not an axiom; the general fix is a
Perennial change (`notes/perennial-changes.md`, 2026-11-14, "`errors.Is` on `fmt.Errorf`'s result").

`errIsNot e t`: `e` is not `t` and `errors.Is(e, t)` returns `false`. Why the triple holds in Go:
`Errorf` returns a fresh `*fmt.wrapError`/`*fmt.wrapErrors` (with `%w`) or a fresh `*errors.errorString`
(`errors.New`, without), so its result is not `t`, a value a package variable held before the call;
neither type has an `Is` method, and its `Unwrap` gives the `%w` arguments, each among `errs`, for which
`errors.Is(_, t)` is false by the premise. Under Perennial's present model (`errors.New(format)`) it holds
too (a fresh `*errorString`, a leaf: `errors.wp_Is_leaf`), but the premise gives no points-to of `t`'s
pointer, so the model's freshness cannot be used against it: hence a hypothesis.
W3a of `notes/wal-fsext-plan.md` (ledger 2026-11-14, "the error's identity"); Lean-first.
-/
module

public import LinuxFs.Spec.fmt.ErrorfErrs

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

/-- See the file header. -/
abbrev fmt.ErrorfErrsNot.spec : Prop :=
  ∀ (format : GoString) (args_sl : GoSlice) (args : List GoAny) (errs : List GoInterfaceOk)
    (X : GoString) (t : GoInterface),
  (∀ ii, interface.ok ii ∈ args → fmt.ArgWf ii ∨ ii ∈ errs) →
    {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗ args_sl ↦* args ∗ globalAddr X ↦□ t ∗
        [∗list] e ∈ errs, errOk e ∗ errIsNot (GoInterface.ok e) t }}
      (App (App (Val (@! _root_.Perennial.fmt.Errorf)) (Val #format)) (Val #args_sl))
    {{ (err : GoInterfaceOk), RET #(interface.ok err); errOk err ∗ errIsNot (GoInterface.ok err) t }}

end spec

end EtcdGrove
end Perennial
