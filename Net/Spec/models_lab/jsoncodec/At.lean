/-
`jsoncodec.At(b, i)`: the index of the first byte after the whitespace at `i`, and that byte. A spec at the inputs the generated decoders
meet (valid JSON), so it implies safety there. Proved in `Net/Proof/models_lab/jsoncodec/At.lean`;
Ported from dsverify-lab's `wp_At` (`examples/vr/proof/VsrProof/Proof/jsoncodec/GoDec.lean`,
lab master 915f964).
-/
module

public import Net.Proof.models_lab.jsoncodec.Base
public import Net.Proof.models_lab.jsoncodec.Scan.Lits
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
abbrev At.spec : Prop :=
  ∀ (b : GoSlice) (dq : DFrac) (bs : List w8) (i : w64) (c : w8)
    (hi : uint.nat i ≤ bs.length) (hc : bs[JsonScan.skipEnd bs (uint.nat i)]? = some c),
  {{ (b ↦*{dq} bs : IProp GF) }}
    (App (App (Val (@! models_lab.jsoncodec.At)) (Val #b)) (Val #i))
  {{ RET (PairV #(W64 ((JsonScan.skipEnd bs (uint.nat i) : Nat) : Int)) #c); b ↦*{dq} bs }}

end spec

end models_lab.jsoncodec
end Perennial
