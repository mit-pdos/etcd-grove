/-
`jsoncodec.seqLenOf(c, c1, c2, c3)`: the length of the valid UTF-8 sequence starting with these bytes,
or 1 (`seqLenB`). Pure.
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
abbrev seqLenOf.spec : Prop :=
  ∀ (c c1 c2 c3 : w8),
  {{ (True : IProp GF) }}
    (App (App (App (App (Val (@! models_lab.jsoncodec.seqLenOf)) (Val #c)) (Val #c1)) (Val #c2))
      (Val #c3))
  {{ RET #(W64 (seqLenB c c1 c2 c3)); True }}

end spec

end models_lab.jsoncodec
end Perennial
