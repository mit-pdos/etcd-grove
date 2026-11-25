/-
`jsoncodec.Scan` computes `JsonScan.scanF`: the codec obligation `scanOk JsonScan.scanF scanFn`
(`Codec.lean`) that every generated codec's registration needs, from `Scan`'s spec
(`Net/Spec/models_lab/jsoncodec/Scan.lean`; linked: `Net/Proof/models_lab/Results.lean`'s
`jsoncodec.scanOk_scanF`). Ported from dsverify-lab's
`examples/vr/proof/VsrProof/Proof/jsoncodec/ScanOk.lean` (lab master 915f964).
-/
module

public import Net.Proof.models_lab.jsoncodec.Codec
public import Net.Proof.models_lab.jsoncodec.Scan.Bounds
public import Net.Spec.models_lab.jsoncodec.Scan

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace models_lab.jsoncodec

/-- `scanF`'s end is within its input. -/
theorem scanF_end_le (bs : List w8) (eof : Bool) :
    uint.nat (JsonScan.scanF bs eof).2 ≤ bs.length := by
  have := JsonScan.scanL_le bs eof
  simp only [JsonScan.scanF]
  have h : uint.nat (W64 ((JsonScan.scanL bs eof).2 : Int)) ≤ (JsonScan.scanL bs eof).2 := by
    simp only [uint.nat, W64, BitVec.toNat_ofInt]
    omega
  omega

section scanOk
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : models_lab.jsoncodec.Assumptions]

/-- `jsoncodec.Scan` computes `JsonScan.scanF`, given `Scan`'s spec. -/
theorem scanOk_of (wp_Scan : Scan.spec (GF := GF) (hG := hG)) :
    ⊢ scanOk (GF := GF) JsonScan.scanF scanFn := by
  unfold scanOk
  isplitr
  · ipureintro
    exact scanF_end_le
  imodintro
  iintro %s %dq %bs %eof %Φ Hs HΦ
  unfold scanFn
  rw [show (go!"models.lab/jsoncodec.Scan" : GoString) = models_lab.jsoncodec.Scan from rfl]
  iapply (wp_Scan s dq bs eof) $$ Hs
  iexact HΦ

end scanOk

end models_lab.jsoncodec
end Perennial
