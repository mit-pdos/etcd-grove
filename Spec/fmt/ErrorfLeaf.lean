/-
`fmt.Errorf(format, args...)` of arguments `fmt.Errorf.spec` admits (`fmt.argsOk` under `Errorf`'s
verbs), **proved** over Perennial's model of `Errorf` (`Proof/fmt/ErrorfLeaf.lean`, listed for review
by the term gate `etc/errorf-wrap-check.py`), with one fact more in the post: the error's dynamic type
has no `Errors` method, so it is no `utilerrors.Aggregate` (2026-11-20, conditional authorization:
`aggregate.Error()`'s `visit` type-switches its elements on `Aggregate`, and the errors the
authorizer package puts in its decisions are aggregated: `Proof/.../util/errors/Defs.lean`'s
`errLeafOk`). `fmt.Errorf.spec` (the trust boundary, `Proof/fmt/Errorf.lean`) does not state it, and
adding a conjunct to its post would change the shape of what its 89 users destructure.

Why the model may be used for these arguments (as for `fmt.ErrorfErrs`, `fmt.ErrorfStrs`): the model
(`errors.New(format)`) departs from Go only in not formatting the arguments, and `fmt.argsOk` admits
only arguments whose formatting calls nothing with an effect or a panic: `nil` and basic values (no
method), named integers under non-method verbs (printed by reflection), values whose `Error()` or
`String()` (no `Format`; under `%w` only `Error() string`) returns some string needing nothing
(`fmt.stringMethodSpec`, persistent), and read-only slices of such values under `%v`/`%s`
(`fmt.sliceArgOk`, whose header traces Go's `printValue`). The post: Go returns a `*fmt.wrapError`
(one `%w`), a `*fmt.wrapErrors` (several) or an `*errors.errorString` (none) (`fmt/errors.go`), whose
method sets are `Error`, `Unwrap` (`errors.go`'s `wrapError`, `wrapErrors`) and `Error`
(`errors/errors.go`): `Error() string`, no `Format`, no `Errors`; `Error()` returns the formatted
message (`errOk`); the model's `*errorString` has the same facts. The arguments' slice is read, and
given back. Lean-first.
-/
module

public import Spec.fmt.ErrorfErrs
public import Spec.fmt.Errorf

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
variable [package_sem : _root_.Perennial.fmt.Assumptions]

/-- See the file header. -/
abbrev fmt.ErrorfLeaf.spec : Prop :=
  ∀ (format : GoString) (args_sl : GoSlice) (xs : List GoInterface) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗ args_sl ↦*{dq} xs ∗ fmt.argsOk fmt.errorfVerbs format xs }}
    (App (App (Val (@! _root_.Perennial.fmt.Errorf)) (Val #format)) (Val #args_sl))
  {{ (err : GoInterfaceOk), RET #(interface.ok err);
      args_sl ↦*{dq} xs ∗ errOk err ∗ ⌜methodSet err.ty !! go!"Errors" = none⌝ }}

end spec

end EtcdGrove
end Perennial
