/-
`jsoncodec.String(b, i)` on a plain string at `i`: its contents, `Set`, the index after it. A spec at the inputs the generated decoders
meet (valid JSON), so it implies safety there. Proved in `Net/Proof/models_lab/jsoncodec/String.lean`;
Ported from dsverify-lab's `wp_String` (`examples/vr/proof/VsrProof/Proof/jsoncodec/GoDec.lean`,
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
abbrev String.spec : Prop :=
  ∀ (b : GoSlice) (dq : DFrac) (bs : List w8) (i : w64) (str rest : List w8)
    (hs : ∀ c ∈ str, JsonScan.okB c) (hb : bs.drop (uint.nat i) = 34#8 :: (str ++ 34#8 :: rest)),
  {{ (b ↦*{dq} bs : IProp GF) }}
    (App (App (Val (@! models_lab.jsoncodec.String)) (Val #b)) (Val #i))
  {{ RET (PairV (PairV #str #(W64 0))
        #(W64 ((uint.nat i + 1 + str.length + 1 : Nat) : Int))); b ↦*{dq} bs }}

end spec

end models_lab.jsoncodec
end Perennial
