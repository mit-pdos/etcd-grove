/-
`field.ErrorList.ToAggregate()` (apimachinery, names only): **the trust boundary**. Lean-first (no
Rocq counterpart).
-/
module

public import GeneratedProof.k8s_io.apimachinery.pkg.util.validation.field

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

/-- See the file header. -/
abbrev ErrorList.ToAggregate.spec : Prop :=
  ∀ (s : GoSlice) (dq : DFrac) (errs : List Loc),
  {{ (s ↦*{dq} errs : IProp GF) }}
    (App (Val (s @!! _root_.Perennial.k8s_io.apimachinery.pkg.util.validation.field.ErrorList.ty @!!
      go!"ToAggregate")) (Val #()))
  {{ (a : GoInterface), RET #a; s ↦*{dq} errs }}

end spec

end field
end EtcdGrove
end Perennial
