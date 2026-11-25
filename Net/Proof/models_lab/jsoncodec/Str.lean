/-
The proof of `jsoncodec.Str` (`Net/Spec/models_lab/jsoncodec/Str.lean`). Ported from dsverify-lab's `wp_Str` (`examples/vr/proof/VsrProof/Proof/jsoncodec/GoDec.lean`,
lab master 915f964).
-/
module

public import Net.Spec.models_lab.jsoncodec.Str
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

theorem Str.wp_proof  :
    Str.spec (GF := GF) (hG := hG) := by
  intro b dq bs i s rest hs hb hi
  wp_start as Hs
  ihave %Hlen := ownSlice_len $$ Hs
  ihave %Hwf := ownSlice_wf $$ Hs
  have hl63 := len_lt b bs Hlen
  have hlen : uint.nat i + 1 + s.length + 1 ≤ bs.length := by
    have := congrArg List.length hb; simp at this; omega
  have hget : ∀ k < s.length, bs[uint.nat i + 1 + k]? = s[k]? := by
    intro k hk
    have := congrArg (fun l => l[k]?) hb
    simp only [List.getElem?_drop] at this
    rw [this, List.getElem?_append_left hk]
  have hq : bs[uint.nat i + 1 + s.length]? = some 34#8 := by
    have := congrArg (fun l => l[s.length]?) hb
    simp only [List.getElem?_drop] at this
    rw [this]; simp
  wp_auto
  ihave IH : iprop(∃ (jw : w64),
      "j" ∷ j_ptr ↦ jw ∗
      "%Hj" ∷ ⌜uint.nat i + 1 ≤ uint.nat jw ∧ uint.nat jw ≤ uint.nat i + 1 + s.length⌝) $$ [j]
  · iexists _; iframe; ipureintro; constructor <;> word
  wp_for IH
  ldidx jw, x, Hx
  by_cases hjs : uint.nat jw < uint.nat i + 1 + s.length
  · have hk : uint.nat jw - (uint.nat i + 1) < s.length := by omega
    have hxs : s[uint.nat jw - (uint.nat i + 1)]? = some x := by
      rw [← hget _ hk, show uint.nat i + 1 + (uint.nat jw - (uint.nat i + 1)) = uint.nat jw by omega]
      exact Hx
    have hok := hs x (List.mem_of_getElem? hxs)
    have hx34 : x ≠ W8 34 := hok.2.2.1
    have hx92 : x ≠ W8 92 := hok.2.2.2
    have hx80 : ¬ uint.Z (W8 128) ≤ uint.Z x := by
      have := hok.2.1; simp only [uint.Z, W8]; simp; omega
    simp only [hx34, decide_false, Bool.not_false, decide_true, ite_true]
    wp_auto
    have Hx2 := Hx
    ldagain jw, Hx2
    wp_if_destruct
    · exact absurd rfl hx92
    have Hx3 := Hx
    ldagain jw, Hx3
    wp_if_destruct
    · exact absurd Hif hx80
    wp_for_post
    iframe
    iexists _
    iframe
    ipureintro
    constructor <;> word
  · have hje : uint.nat jw = uint.nat i + 1 + s.length := by omega
    have hx : x = 34#8 := by rw [hje, hq] at Hx; cases Hx; rfl
    subst hx
    simp only [show (34#8 : w8) = W8 34 from rfl, decide_true, Bool.not_true]
    simp
    rw [if_neg (fun h => by have := go.intoVal_inj h; simp at this)]
    wp_auto
    have hb1 : 0 ≤ sint.Z (i + 1#64) ∧ sint.Z (i + 1#64) ≤ sint.Z jw ∧ sint.Z jw ≤ sint.Z b.cap := by
      word
    rw [if_pos hb1]
    have hb2 : 0 ≤ sint.Z (i + 1#64) ∧ sint.Z (i + 1#64) ≤ sint.Z jw ∧ sint.Z jw ≤ sint.Z b.len := by
      word
    icases (ownSlice_slice (i + 1#64) jw b dq bs hb2).1 $$ Hs with ⟨H1, H2, H3⟩
    have hsub : subslice (sint.nat (i + 1#64)) (sint.nat jw) bs = s := by
      rw [show sint.nat (i + 1#64) = uint.nat i + 1 by word, show sint.nat jw = uint.nat i + 1 + s.length by word]
      simp only [subslice, List.drop_take]
      rw [hb]; simp
    rw [hsub]
    wp_apply wp_bytes_to_string _ s dq $$ H2 as H2
    ihave Hs := (ownSlice_slice (i + 1#64) jw b dq bs hb2).2 $$ [H1 H2 H3]
    · rw [hsub]; iframe
    rw [show jw + 1#64 = W64 (↑(uint.nat i) + 1 + ↑s.length + 1) by word]
    iapply HΦ
    iexact Hs
end proof

end models_lab.jsoncodec
end Perennial
