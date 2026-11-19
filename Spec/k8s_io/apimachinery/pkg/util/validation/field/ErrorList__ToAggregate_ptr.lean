/-
`(*field.ErrorList).ToAggregate()`, the pointer-receiver wrapper Go generates for the value method
`ErrorList.ToAggregate` (`errs.ToAggregate()` on an addressable local `errs`, as
`authorizer.validateConditions`'s): **the trust boundary**, a local workaround (the `field` package
is names-only, and goose then omits `ptr_ToAggregate_unfold` too, so the translation does not relate
the two; see `notes/perennial-changes.md`). Lean-first (no Rocq counterpart).
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

/-- `l.ToAggregate()` (from the value method's spec, see the axiom) loads the list `*l` (read at any fraction, kept) and is the value method on
it (`ErrorList.ToAggregate.spec`): some error, the list's elements kept. -/
abbrev ErrorList.ToAggregate_ptr.spec : Prop :=
  ∀ (l : Loc) (dl : DFrac) (s : GoSlice) (dq : DFrac) (errs : List Loc),
  {{ (l ↦{dl} s ∗ s ↦*{dq} errs : IProp GF) }}
    (App (Val (l @!! go.GoType.PointerType
      _root_.Perennial.k8s_io.apimachinery.pkg.util.validation.field.ErrorList.ty @!!
      go!"ToAggregate")) (Val #()))
  {{ (a : GoInterface), RET #a; l ↦{dl} s ∗ s ↦*{dq} errs }}

end spec

end field
end EtcdGrove
end Perennial
