/-
The proof of `jsoncodec.At` (`Net/Spec/models_lab/jsoncodec/At.lean`). Ported from dsverify-lab's `wp_At` (`examples/vr/proof/VsrProof/Proof/jsoncodec/GoDec.lean`,
lab master 915f964).
-/
module

public import Net.Spec.models_lab.jsoncodec.At
public import Net.Spec.models_lab.jsoncodec.SkipSpace
public import Net.Proof.models_lab.jsoncodec.DecBase

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.iris.style.nameCheck false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace models_lab.jsoncodec

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : models_lab.jsoncodec.Assumptions]

set_option goose.wp.extras true
set_option maxHeartbeats 2000000

theorem At.wp_proof (wp_SkipSpace : SkipSpace.spec (GF := GF) (hG := hG)) :
    At.spec (GF := GF) (hG := hG) := by
  intro b dq bs i c hi hc
  wp_start as Hs
  ihave %Hlen := ownSlice_len $$ Hs
  have hl63 := len_lt b bs Hlen
  have hsk : JsonScan.skipEnd bs (uint.nat i) < bs.length := by
    rcases Nat.lt_or_ge (JsonScan.skipEnd bs (uint.nat i)) bs.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hc; cases hc
  wp_auto
  wp_apply (wp_SkipSpace b dq bs i hi) $$ Hs as Hs
  generalize JsonScan.skipEnd bs (uint.nat i) = j at hc hsk ⊢
  have hz : uint.nat (W64 (j : Int)) = j := by word
  ldidx (W64 (j : Int)), c', Hc'
  rw [hz, hc] at Hc'
  cases Hc'
  iapply HΦ
  iexact Hs
end proof

end models_lab.jsoncodec
end Perennial
