/-
`jsoncodec.Nesting(b)`: `nestRun 0 0 false bs` (`Compact.lean`), the deepest nesting of arrays and
objects outside strings, for any bytes. Proved in `Net/Proof/models_lab/jsoncodec/Nesting.lean`
(dsv-vr round 9).
-/
module

public import Net.Proof.models_lab.jsoncodec.Base
public import Net.Proof.models_lab.jsoncodec.Compact

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
abbrev Nesting.spec : Prop :=
  ∀ (b : GoSlice) (dq : DFrac) (bs : List w8),
  {{ (b ↦*{dq} bs : IProp GF) }}
    (App (Val (@! models_lab.jsoncodec.Nesting)) (Val #b))
  {{ RET #(nestRun (W64 0) (W64 0) false bs); b ↦*{dq} bs }}

end spec

end models_lab.jsoncodec
end Perennial
