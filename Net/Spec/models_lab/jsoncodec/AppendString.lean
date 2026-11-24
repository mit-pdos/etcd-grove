/-
`jsoncodec.AppendString(b, s)`: `b` with `jsonQuote s` after it, real encoding/json's JSON string
for `s` (a slice with its capacity, owned whole). Never panics.
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
abbrev AppendString.spec : Prop :=
  ∀ (b : GoSlice) (bs : List w8) (s : GoString),
  {{ (b ↦* bs ∗ ownSliceCap w8 b (DFrac.own 1) : IProp GF) }}
    (App (App (Val (@! models_lab.jsoncodec.AppendString)) (Val #b)) (Val #s))
  {{ (b' : GoSlice), RET #b'; b' ↦* (bs ++ jsonQuote s) ∗ ownSliceCap w8 b' (DFrac.own 1) }}

end spec

end models_lab.jsoncodec
end Perennial
