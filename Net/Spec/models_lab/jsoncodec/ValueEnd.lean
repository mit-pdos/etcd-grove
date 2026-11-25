/-
`jsoncodec.ValueEnd(b, i)`, a complete value at `i` (as the decoders' valid input has): `i`
plus the end `Scan` finds in `b[i:]`. A spec at the inputs the generated decoders
meet (valid JSON), so it implies safety there. Proved in `Net/Proof/models_lab/jsoncodec/ValueEnd.lean`;
Ported from dsverify-lab's `wp_ValueEnd` (`examples/vr/proof/VsrProof/Proof/jsoncodec/GoDec.lean`,
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
abbrev ValueEnd.spec : Prop :=
  ∀ (b : GoSlice) (dq : DFrac) (bs : List w8) (i : w64)
    (hi : uint.nat i ≤ bs.length) (hd : (JsonScan.scanL (bs.drop (uint.nat i)) true).1 = 0),
  {{ (b ↦*{dq} bs : IProp GF) }}
    (App (App (Val (@! models_lab.jsoncodec.ValueEnd)) (Val #b)) (Val #i))
  {{ RET #(W64 ((uint.nat i + (JsonScan.scanL (bs.drop (uint.nat i)) true).2 : Nat) : Int));
      b ↦*{dq} bs }}

end spec

end models_lab.jsoncodec
end Perennial
