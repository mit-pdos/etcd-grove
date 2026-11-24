/-
`jsoncodec.htmlByte(c)`: whether `c` is `<`, `>` or `&` (`htmlB`). Pure.
-/
module

public import Net.Proof.models_lab.jsoncodec.Quote

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace models_lab.jsoncodec

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : models_lab.jsoncodec.Assumptions]

/-- See the file header. -/
abbrev htmlByte.spec : Prop :=
  ∀ (c : w8),
  {{ (True : IProp GF) }}
    (App (Val (@! models_lab.jsoncodec.htmlByte)) (Val #c))
  {{ RET #(htmlB c); True }}

end spec

end models_lab.jsoncodec
end Perennial
