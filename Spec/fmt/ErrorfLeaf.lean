/-
`fmt.Errorf(format, args...)` of arguments Perennial's `fmt.Errorf` spec admits (`fmt.argsOk` under
`Errorf`'s verbs), with one fact more in the post: the error's dynamic type has no `Errors` method, so
it is no `utilerrors.Aggregate` (2026-11-20, conditional authorization: `aggregate.Error()`'s `visit`
type-switches its elements on `Aggregate`, and the errors the authorizer package puts in its decisions
are aggregated: `Proof/.../util/errors/Defs.lean`'s `errLeafOk`). **Proved** from Perennial's
`fmt.wp_Errorf` (`Proof/fmt/ErrorfLeaf.lean`; fmtmodel, 2026-11-20): Go returns a `*fmt.wrapError`
(one `%w`), a `*fmt.wrapErrors` (several) or an `*errors.errorString` (none) (`fmt/errors.go`), with
method sets `Error`, `Unwrap` and `Error`: `Error() string`, no `Format`, no `Errors`; `Error()`
returns the formatted message (`errOk`). The arguments' slice is read, and given back. (Until fmtmodel,
proved over Perennial's previous model, `errors.New(format)`, and `fmt.argsOk` admitted read-only
slices under `%v`/`%s`; those calls used the axiom `fmt.ErrorfSlice`, false of the real `fmt` and
retired 2026-11-24: the k8s fork spells those slices out, mit-pdos/etcd-grove#9.) Lean-first.
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
