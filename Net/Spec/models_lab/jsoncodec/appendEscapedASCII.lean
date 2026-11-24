/-
`jsoncodec.appendEscapedASCII(b, c)`: `b` with `escASCII c` after it (a slice with its capacity,
owned whole).
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
abbrev appendEscapedASCII.spec : Prop :=
  ∀ (b : GoSlice) (bs : List w8) (c : w8),
  {{ (b ↦* bs ∗ ownSliceCap w8 b (DFrac.own 1) : IProp GF) }}
    (App (App (Val (@! models_lab.jsoncodec.appendEscapedASCII)) (Val #b)) (Val #c))
  {{ (b' : GoSlice), RET #b'; b' ↦* (bs ++ escASCII c) ∗ ownSliceCap w8 b' (DFrac.own 1) }}

end spec

end models_lab.jsoncodec
end Perennial
