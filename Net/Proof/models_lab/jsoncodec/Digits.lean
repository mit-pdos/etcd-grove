/-
The proof of `jsoncodec.Digits` (`Net/Spec/models_lab/jsoncodec/Digits.lean`). Ported from dsverify-lab's `wp_Digits` (`examples/vr/proof/VsrProof/Proof/jsoncodec/GoDec.lean`,
lab master 915f964).
-/
module

public import Net.Spec.models_lab.jsoncodec.Digits
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

theorem Digits.wp_proof  :
    Digits.spec (GF := GF) (hG := hG) := by
  intro b dq bs i j mx hij hj hd hv
  wp_start as Hs
  ihave %Hlen := ownSlice_len $$ Hs
  have hl63 := len_lt b bs Hlen
  generalize hds : (bs.drop (uint.nat i)).take (uint.nat j - uint.nat i) = ds at hd hv ⊢
  have hdl : ds.length = uint.nat j - uint.nat i := by rw [← hds]; simp; omega
  have hget : ∀ m < ds.length, bs[uint.nat i + m]? = ds[m]? := by
    intro m hm; rw [← hds]; simp [List.getElem?_take, List.getElem?_drop]; omega
  have hpre : ∀ m, JsonScan.valD (ds.take m) ≤ JsonScan.valD ds := by
    intro m; conv => rhs; rw [← List.take_append_drop m ds]
    exact JsonScan.valD_le_append _ _
  wp_auto
  wp_if_destruct
  · exfalso; word
  ihave IH : iprop(∃ (kw : w64),
      "k" ∷ k_ptr ↦ kw ∗ "x" ∷ x_ptr ↦ W64 (JsonScan.valD (ds.take (uint.nat kw - uint.nat i)) : Int) ∗
      "%Hk" ∷ ⌜uint.nat i ≤ uint.nat kw ∧ uint.nat kw ≤ uint.nat j⌝) $$ [k x]
  · iexists _; iframe
    rw [Nat.sub_self, List.take_zero]
    iframe
    ipureintro; omega
  wp_for IH
  wp_if_destruct
  · have hm : uint.nat kw - uint.nat i < ds.length := by word
    obtain ⟨c, hc⟩ : ∃ c, ds[uint.nat kw - uint.nat i]? = some c := ⟨_, List.getElem?_eq_getElem hm⟩
    have hbc : bs[uint.nat kw]? = some c := by
      rw [show uint.nat kw = uint.nat i + (uint.nat kw - uint.nat i) by omega, hget _ hm, hc]
    have hcd : JsonScan.isDig c = true := hd c (List.mem_of_getElem? hc)
    ldidx kw, c', Hc'
    rw [hbc] at Hc'; cases Hc'
    wp_apply wp_isDigit c
    simp only [hcd]
    wp_auto
    have hstep := valD_take_succ ds _ c hc
    have hle := hpre (uint.nat kw - uint.nat i + 1)
    have hcn : 48 ≤ c.toNat ∧ c.toNat ≤ 57 := by
      simp only [JsonScan.isDig, Bool.and_eq_true, decide_eq_true_eq, BitVec.le_def] at hcd
      simp at hcd; omega
    wp_if_destruct
    · exfalso
      have hX : JsonScan.valD (List.take (uint.nat kw - uint.nat i) ds) * 10 + (c.toNat - 48) ≤
          uint.nat mx := by omega
      have hD : uint.Z (W64 (uint.Z (c - W8 48))) = (c.toNat - 48 : Nat) := by
        simp only [uint.Z, W8, W64]; simp; omega
      have hXz : uint.Z (W64 ↑(JsonScan.valD (List.take (uint.nat kw - uint.nat i) ds))) =
          (JsonScan.valD (List.take (uint.nat kw - uint.nat i) ds) : Int) := by word
      have hdiv : uint.Z ((mx - W64 (uint.Z (c - W8 48))) / W64 10) =
          (uint.Z mx - (c.toNat - 48 : Nat)) / 10 := by
        have hDm : (c.toNat - 48 : Nat) ≤ uint.nat mx := by omega
        have h1 : uint.Z (mx - W64 (uint.Z (c - W8 48))) = uint.Z mx - (c.toNat - 48 : Nat) := by
          word
        simp only [uint.Z] at h1 ⊢
        rw [BitVec.toNat_udiv]
        simp only [W64] at h1 ⊢
        push_cast [h1]
        simp
      rw [hdiv, hXz] at Hif
      simp only [uint.nat, uint.Z] at hX Hif
      omega
    wp_for_post
    iframe
    iexists _
    rw [show uint.nat (kw + W64 1) - uint.nat i = uint.nat kw - uint.nat i + 1 by word, hstep]
    iframe
    rw [show W64 ((JsonScan.valD (ds.take (uint.nat kw - uint.nat i)) * 10 + (c.toNat - 48) : Nat) : Int)
      = W64 (JsonScan.valD (ds.take (uint.nat kw - uint.nat i)) : Int) * W64 10 + W64 ((c - W8 48).toNat : Int) by word]
    iframe
    ipureintro; word
  · have hk : uint.nat kw = uint.nat j := by word
    rw [hk, ← hdl, List.take_length]
    iapply HΦ; iexact Hs
end proof

end models_lab.jsoncodec
end Perennial
