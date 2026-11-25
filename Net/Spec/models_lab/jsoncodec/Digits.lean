/-
`jsoncodec.Digits(b, i, j, max)` on decimal digits `b[i:j]` (at least one) of value at most
`max`: the value (`valD`) and `true`. A spec at the inputs the generated decoders
meet (valid JSON), so it implies safety there. Proved in `Net/Proof/models_lab/jsoncodec/Digits.lean`;
Ported from dsverify-lab's `wp_Digits` (`examples/vr/proof/VsrProof/Proof/jsoncodec/GoDec.lean`,
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
abbrev Digits.spec : Prop :=
  ∀ (b : GoSlice) (dq : DFrac) (bs : List w8) (i j mx : w64)
    (hij : uint.nat i < uint.nat j) (hj : uint.nat j ≤ bs.length)
    (hd : ∀ c ∈ (bs.drop (uint.nat i)).take (uint.nat j - uint.nat i), JsonScan.isDig c = true)
    (hv : JsonScan.valD ((bs.drop (uint.nat i)).take (uint.nat j - uint.nat i)) ≤ uint.nat mx),
  {{ (b ↦*{dq} bs : IProp GF) }}
    (App (App (App (App (Val (@! models_lab.jsoncodec.Digits)) (Val #b)) (Val #i))
      (Val #j)) (Val #mx))
  {{ RET (PairV #(W64 (JsonScan.valD ((bs.drop (uint.nat i)).take (uint.nat j - uint.nat i)) : Int))
      #true); b ↦*{dq} bs }}

end spec

end models_lab.jsoncodec
end Perennial
