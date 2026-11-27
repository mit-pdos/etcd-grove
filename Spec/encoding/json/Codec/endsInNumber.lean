/-
`endsInNumber(b)` (the encoding/json model's, `v2_stream.go`): some answer, reading `b`, of length
below `2^62` (the loop's index steps past `len(b)` by two after an escape, which would wrap at
`2^63`; `Decoder.readValue` asks it of its buffer, whose capacity is below `2^63 / 3`). Either
answer leads `readValue` to an error, so the spec says nothing of which.
Lean-first (no Rocq counterpart).
-/
module

public import Proof.encoding.json.Registry

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace encoding.json

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : encoding.json.Assumptions]

/-- See the file header. -/
abbrev endsInNumber.spec : Prop :=
  ∀ (b : GoSlice) (dq : DFrac) (bs : List w8), sint.Z b.len < 2 ^ 62 →
  {{ (b ↦*{dq} bs : IProp GF) }}
    (App (Val (@! encoding.json.endsInNumber)) (Val #b))
  {{ (r : Bool), RET #r; b ↦*{dq} bs }}

end spec

end encoding.json
end Perennial
