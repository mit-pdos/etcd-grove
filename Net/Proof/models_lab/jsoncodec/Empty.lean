/-
The proof of `jsoncodec.Empty` (`Net/Spec/models_lab/jsoncodec/Empty.lean`). Ported from dsverify-lab's `wp_Empty` (`examples/vr/proof/VsrProof/Proof/jsoncodec/GoDec.lean`,
lab master 915f964).
-/
module

public import Net.Spec.models_lab.jsoncodec.Empty
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

theorem Empty.wp_proof (wp_SkipSpace : SkipSpace.spec (GF := GF) (hG := hG)) :
    Empty.spec (GF := GF) (hG := hG) := by
  intro b dq bs i c hi hc
  rcases Classical.em (c = W8 93 ∨ c = W8 125) with hcc | hcc <;>
    simp only [hcc, if_true, if_false, ite_true, ite_false]
  all_goals
    wp_start as Hs
    ihave %Hlen := ownSlice_len $$ Hs
    have hl63 := len_lt b bs Hlen
    have hsk : JsonScan.skipEnd bs (uint.nat i + 1) < bs.length := by
      rcases Nat.lt_or_ge (JsonScan.skipEnd bs (uint.nat i + 1)) bs.length with h | h
      · exact h
      · rw [List.getElem?_eq_none h] at hc; cases hc
    wp_auto
    wp_apply (wp_SkipSpace b dq bs (i + W64 1) (by word)) $$ Hs as Hs
    rw [show uint.nat (i + W64 1) = uint.nat i + 1 by word]
    generalize JsonScan.skipEnd bs (uint.nat i + 1) = j at hc hsk ⊢
    have hz : uint.nat (W64 (j : Int)) = j := by word
    ldidx (W64 (j : Int)), c', Hc'
    rw [hz, hc] at Hc'
    cases Hc'
    wp_if_destruct
    · (try rw [show W64 ((j + 1 : Nat) : Int) = W64 (j : Int) + W64 1 by word] at *)
      first | (iapply HΦ; iexact Hs) | (exfalso; exact hcc (Or.inl rfl))
    have Hc2 : bs[uint.nat (W64 (j : Int))]? = some c := by rw [hz, hc]
    ldagain (W64 (j : Int)), Hc2
    wp_if_destruct
    · (try rw [show W64 ((j + 1 : Nat) : Int) = W64 (j : Int) + W64 1 by word] at *)
      first | (iapply HΦ; iexact Hs) | (exfalso; exact hcc (Or.inr rfl))
    first | (iapply HΦ; iexact Hs) | (exfalso; rcases hcc with h | h <;> contradiction)
end proof

end models_lab.jsoncodec
end Perennial
