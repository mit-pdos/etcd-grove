/-
`(*field.ErrorList).ToAggregate()`, the pointer-receiver wrapper Go generates for the value method
`ErrorList.ToAggregate` (`errs.ToAggregate()` on an addressable local `errs`, as
`authorizer.validateConditions`'s): goose's `ptr_unfold'ToAggregate` (since `ToAggregate` is
translated with its body, 2026-11-19; until then this was a trust-boundary workaround) makes it load
`*l` and run the value method, so it is proved from `ErrorList.ToAggregate.spec`, whose premises it
shares. Lean-first (no Rocq counterpart).
-/
module

public import Spec.k8s_io.apimachinery.pkg.util.validation.field.ErrorList__ToAggregate

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

/-- `l.ToAggregate()` loads the list `*l` (read at any fraction, kept) and is the value method on
it (`ErrorList.ToAggregate.spec`): some error, the list's elements kept. -/
abbrev ErrorList.ToAggregate_ptr.spec : Prop :=
  ∀ (l : Loc) (dl : DFrac) (s : GoSlice) (dq : DFrac) (errs : List Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.validation.field ∗
      l ↦{dl} s ∗ s ↦*{dq} errs ∗ [∗list] e ∈ errs, errorOk e }}
    (App (Val (l @!! go.GoType.PointerType
      _root_.Perennial.k8s_io.apimachinery.pkg.util.validation.field.ErrorList.ty @!!
      go!"ToAggregate")) (Val #()))
  {{ (a : GoInterface), RET #a; l ↦{dl} s ∗ s ↦*{dq} errs ∗ utilerrors.errTreeOrNil a }}

end spec

end field
end EtcdGrove
end Perennial
