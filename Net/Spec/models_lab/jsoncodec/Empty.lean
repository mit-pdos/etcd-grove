/-
`jsoncodec.Empty(b, i)` (an opening bracket at `i`): whether the container closes right away
(after whitespace), with the index after the closing bracket, else `i + 1`. A spec at the inputs the generated decoders
meet (valid JSON), so it implies safety there. Proved in `Net/Proof/models_lab/jsoncodec/Empty.lean`;
Ported from dsverify-lab's `wp_Empty` (`examples/vr/proof/VsrProof/Proof/jsoncodec/GoDec.lean`,
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
abbrev Empty.spec : Prop :=
  ∀ (b : GoSlice) (dq : DFrac) (bs : List w8) (i : w64) (c : w8)
    (hi : uint.nat i < bs.length) (hc : bs[JsonScan.skipEnd bs (uint.nat i + 1)]? = some c),
  {{ (b ↦*{dq} bs : IProp GF) }}
    (App (App (Val (@! models_lab.jsoncodec.Empty)) (Val #b)) (Val #i))
  {{ RET (if c = W8 93 ∨ c = W8 125 then
        PairV #true #(W64 ((JsonScan.skipEnd bs (uint.nat i + 1) + 1 : Nat) : Int))
      else PairV #false #(i + W64 1)); b ↦*{dq} bs }}

end spec

end models_lab.jsoncodec
end Perennial
