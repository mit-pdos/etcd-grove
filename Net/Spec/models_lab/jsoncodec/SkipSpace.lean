/-
`jsoncodec.SkipSpace(b, i)` (`i` within `b`): the index after the whitespace run at `i`
(`JsonScan.skipEnd`). A functional spec (no panic). Proved in
`Net/Proof/models_lab/jsoncodec/SkipSpace.lean`; ported from dsverify-lab's `wp_SkipSpace`
(`examples/vr/proof/VsrProof/Proof/jsoncodec/GoBase.lean`, lab master 915f964).
-/
module

public import Net.Proof.models_lab.jsoncodec.Base
public import Net.Proof.models_lab.jsoncodec.Scan.Idx

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
abbrev SkipSpace.spec : Prop :=
  ∀ (b : GoSlice) (dq : DFrac) (bs : List w8) (i : w64), uint.nat i ≤ bs.length →
  {{ (b ↦*{dq} bs : IProp GF) }}
    (App (App (Val (@! models_lab.jsoncodec.SkipSpace)) (Val #b)) (Val #i))
  {{ RET #(W64 (JsonScan.skipEnd bs (uint.nat i) : Int)); b ↦*{dq} bs }}

end spec

end models_lab.jsoncodec
end Perennial
