/-
The proof of `jsoncodec.ValueEnd` (`Net/Spec/models_lab/jsoncodec/ValueEnd.lean`). Ported from dsverify-lab's `wp_ValueEnd` (`examples/vr/proof/VsrProof/Proof/jsoncodec/GoDec.lean`,
lab master 915f964).
-/
module

public import Net.Spec.models_lab.jsoncodec.ValueEnd
public import Net.Spec.models_lab.jsoncodec.Scan
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

theorem ValueEnd.wp_proof (wp_Scan : Scan.spec (GF := GF) (hG := hG)) :
    ValueEnd.spec (GF := GF) (hG := hG) := by
  intro b dq bs i hi hd
  wp_start as Hs
  ihave %Hlen := ownSlice_len $$ Hs
  ihave %Hwf := ownSlice_wf $$ Hs
  have hl63 := len_lt b bs Hlen
  simp only [models_lab.jsoncodec.Done]
  wp_auto
  have hb : 0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z b.len ∧ sint.Z b.len ≤ sint.Z b.cap := by word
  rw [if_pos hb]
  have hb2 : 0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z b.len ∧ sint.Z b.len ≤ sint.Z b.len := by word
  icases (ownSlice_slice i b.len b dq bs hb2).1 $$ Hs with ⟨H1, H2, H3⟩
  have hsub : subslice (sint.nat i) (sint.nat b.len) bs = bs.drop (uint.nat i) := by
    rw [show sint.nat i = uint.nat i by word, show sint.nat b.len = bs.length by word]
    simp [subslice]
  rw [hsub]
  wp_apply (wp_Scan _ dq (bs.drop (uint.nat i)) true) $$ H2 as H2
  try simp only [JsonScan.scanF]
  have hle := JsonScan.scanL_le (bs.drop (uint.nat i)) true
  simp only [List.length_drop] at hle
  rw [hd]
  wp_auto
  ihave Hs := (ownSlice_slice i b.len b dq bs hb2).2 $$ [H1 H2 H3]
  · rw [hsub]; iframe
  iapply w64_finish Φ _ _ _ (by word) $$ HΦ
  iexact Hs
end proof

end models_lab.jsoncodec
end Perennial
