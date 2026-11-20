/-
`field.ErrorList.ToAggregate()` (`errors.go`, translated with its body; proved,
`Proof/.../field/ErrorList__ToAggregate.lean`): some `Aggregate` (`nil` for an empty list, else
`utilerrors.NewAggregate` of the errors with distinct messages), the list kept. It formats each
error, `fmt.Sprintf("%v", err)`, which calls its `Error()`: hence the premise that each is
`field.errorOk` (read-only, a known type, a string bad value: `Spec/.../field/ErrorOk.lean`) and
`field`'s initialization (2026-11-19: until then a names-only trust boundary without them).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.k8s_io.apimachinery.pkg.util.validation.field.ErrorOk

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace field

open Iris Iris.BI 

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.k8s_io.apimachinery.pkg.util.validation.field.Assumptions]

/-- See the file header. -/
abbrev ErrorList.ToAggregate.spec : Prop :=
  ∀ (s : GoSlice) (dq : DFrac) (errs : List Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.validation.field ∗
      s ↦*{dq} errs ∗ [∗list] e ∈ errs, errorOk e }}
    (App (Val (s @!! _root_.Perennial.k8s_io.apimachinery.pkg.util.validation.field.ErrorList.ty @!!
      go!"ToAggregate")) (Val #()))
  {{ (a : GoInterface), RET #a; s ↦*{dq} errs }}

end spec

end field
end EtcdGrove
end Perennial
