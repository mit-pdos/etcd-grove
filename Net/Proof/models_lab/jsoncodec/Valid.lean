/-
The proof of `jsoncodec.Valid` (`Net/Spec/models_lab/jsoncodec/Valid.lean`) on one complete value.
Ported from dsverify-lab's `wp_Valid_ok` (`GoEnc.lean`, lab master 915f964).
-/
module

public import Net.Spec.models_lab.jsoncodec.Valid
public import Net.Spec.models_lab.jsoncodec.Scan
public import Net.Spec.models_lab.jsoncodec.SkipSpace
public import Net.Proof.models_lab.jsoncodec.ScanString

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

theorem Valid.wp_proof (wp_Scan : Scan.spec (GF := GF) (hG := hG))
    (wp_SkipSpace : SkipSpace.spec (GF := GF) (hG := hG)) :
    Valid.spec (GF := GF) (hG := hG) := by
  intro b dq bs hsc
  wp_start as Hs
  ihave %Hlen := ownSlice_len $$ Hs
  have hl63 := len_lt b bs Hlen
  wp_auto
  wp_apply (wp_Scan b dq bs true) $$ Hs as Hs
  try simp only [JsonScan.scanF]
  rw [hsc]
  wp_auto
  wp_apply (wp_SkipSpace b dq bs (W64 (bs.length : Int)) (by word)) $$ Hs as Hs
  rw [show uint.nat (W64 (bs.length : Int)) = bs.length by word]
  simp only [JsonScan.skipEnd, List.drop_length, List.takeWhile_nil, List.length_nil, Nat.add_zero]
  ihave %Hwf := ownSlice_wf $$ Hs
  rw [decide_eq_true (show W64 (bs.length : Int) = b.len by word)]
  iapply HΦ
  iframe
end proof

end models_lab.jsoncodec
end Perennial
