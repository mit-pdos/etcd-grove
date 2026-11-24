/-
`jsoncodec.seqLen(s, i)`, `i` within `s`: the length of the valid UTF-8 sequence at `s[i]`, or 1
(`seqLenAt`).
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
abbrev seqLen.spec : Prop :=
  ∀ (s : GoString) (i : w64), uint.nat i < s.length →
  {{ (True : IProp GF) }}
    (App (App (Val (@! models_lab.jsoncodec.seqLen)) (Val #s)) (Val #i))
  {{ RET #(W64 (seqLenAt s (uint.nat i))); True }}

end spec

end models_lab.jsoncodec
end Perennial
