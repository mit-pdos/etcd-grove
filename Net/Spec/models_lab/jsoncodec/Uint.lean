/-
`jsoncodec.Uint(b, i, max)` on the decimal digits of `n ≤ max` at `i` (`decN n`), then a byte
ending the number: `n`, `Set`, the index after the digits. A spec at the inputs the generated decoders
meet (valid JSON), so it implies safety there. Proved in `Net/Proof/models_lab/jsoncodec/Uint.lean`;
Ported from dsverify-lab's `wp_Uint` (`examples/vr/proof/VsrProof/Proof/jsoncodec/GoDec.lean`,
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
abbrev Uint.spec : Prop :=
  ∀ (b : GoSlice) (dq : DFrac) (bs : List w8) (i mx : w64) (n : Nat) (c : w8)
    (rest : List w8) (hc : JsonScan.numEnd c)
    (hb : bs.drop (uint.nat i) = JsonScan.decN n ++ c :: rest) (hn : n ≤ uint.nat mx),
  {{ (b ↦*{dq} bs : IProp GF) }}
    (App (App (App (Val (@! models_lab.jsoncodec.Uint)) (Val #b)) (Val #i)) (Val #mx))
  {{ RET (PairV (PairV #(W64 (n : Int)) #(W64 0))
        #(W64 ((uint.nat i + (JsonScan.decN n).length : Nat) : Int))); b ↦*{dq} bs }}

end spec

end models_lab.jsoncodec
end Perennial
