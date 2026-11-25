/-
The proof of `jsoncodec.QuotedUint` (`Net/Spec/models_lab/jsoncodec/QuotedUint.lean`). Ported from dsverify-lab's `wp_QuotedUint` (`examples/vr/proof/VsrProof/Proof/jsoncodec/GoDec.lean`,
lab master 915f964).
-/
module

public import Net.Spec.models_lab.jsoncodec.QuotedUint
public import Net.Spec.models_lab.jsoncodec.At
public import Net.Spec.models_lab.jsoncodec.ValueEnd
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

theorem QuotedUint.wp_proof (wp_At : At.spec (GF := GF) (hG := hG)) (wp_ValueEnd : ValueEnd.spec (GF := GF) (hG := hG)) (wp_Digits : Digits.spec (GF := GF) (hG := hG)) :
    QuotedUint.spec (GF := GF) (hG := hG) := by
  intro b dq bs i mx n rest hb hn
  wp_start as Hs
  ihave %Hlen := ownSlice_len $$ Hs
  have hl63 := len_lt b bs Hlen
  have hlen : uint.nat i + (JsonScan.decN n).length + 2 ≤ bs.length := by
    have := congrArg List.length hb; simp at this; omega
  have h0 : bs[uint.nat i]? = some 34#8 := by
    have := congrArg (fun l => l[0]?) hb; simp only [List.getElem?_drop] at this; simpa using this
  have hsk : JsonScan.skipEnd bs (uint.nat i) = uint.nat i := skipEnd_ns' bs _ _ h0 (by decide)
  simp only [models_lab.jsoncodec.Set', models_lab.jsoncodec.Keep,
    models_lab.jsoncodec.TypeErr]
  wp_auto
  wp_apply (wp_At b dq bs i _ (by omega) (by rw [hsk]; exact h0)) $$ Hs as Hs
  rw [hsk, show W64 ((uint.nat i : Nat) : Int) = i by word]
  have hsc : JsonScan.scanL (bs.drop (uint.nat i)) true = (0, (JsonScan.decN n).length + 2) := by
    rw [hb]; exact JsonScan.scanL_str (JsonScan.decN n) rest (JsonScan.decN_okB n)
  wp_apply (wp_ValueEnd b dq bs i (by omega) (by rw [hsc])) $$ Hs as Hs
  rw [hsc]
  simp only
  obtain ⟨d, ds, hdn⟩ : ∃ d ds, JsonScan.decN n = d :: ds := by
    cases h : JsonScan.decN n with
    | nil => exact absurd h (JsonScan.decN_ne_nil n)
    | cons d ds => exact ⟨d, ds, rfl⟩
  have hdd : JsonScan.isDig d = true := JsonScan.decN_digits n d (by rw [hdn]; simp)
  have h1 : bs[uint.nat (i + W64 1)]? = some d := by
    have := congrArg (fun l => l[1]?) hb; simp only [List.getElem?_drop] at this
    rw [show uint.nat (i + W64 1) = uint.nat i + 1 by word]; simpa [hdn] using this
  have hd110 : d ≠ W8 110 := by
    intro h; subst h; exact absurd hdd (by decide)
  have hne : ∀ (k : Nat) (x : w8), uint.nat (i + W64 1) ≤ k →
      k < uint.nat (W64 ((uint.nat i + ((JsonScan.decN n).length + 2) : Nat) : Int) - W64 1) →
      bs[k]? = some x → x ≠ W8 92 := by
    intro k x hk1 hk2 hx
    rw [show uint.nat (i + W64 1) = uint.nat i + 1 by word] at hk1
    rw [show uint.nat (W64 ((uint.nat i + ((JsonScan.decN n).length + 2) : Nat) : Int) - W64 1) =
      uint.nat i + (JsonScan.decN n).length + 1 by word] at hk2
    have h := congrArg (fun l => l[k - uint.nat i]?) hb
    simp only [List.getElem?_drop] at h
    rw [show uint.nat i + (k - uint.nat i) = k by omega, hx,
      show k - uint.nat i = (k - uint.nat i - 1) + 1 by omega, List.getElem?_cons_succ,
      List.getElem?_append_left (by omega)] at h
    have hdg := JsonScan.decN_digits n x (List.mem_of_getElem? h.symm)
    intro hx92; subst hx92; exact absurd hdg (by decide)
  wp_apply (wp_noEscape b dq bs (i + W64 1)
    (W64 ((uint.nat i + ((JsonScan.decN n).length + 2) : Nat) : Int) - W64 1) (by word) hne) $$ Hs as Hs
  wp_if_destruct
  · ldagain (i + W64 1), h1
    simp only [hd110, decide_false]
    wp_auto
    have hdg : (bs.drop (uint.nat (i + W64 1))).take
        (uint.nat (W64 ((uint.nat i + ((JsonScan.decN n).length + 2) : Nat) : Int) - W64 1) -
          uint.nat (i + W64 1)) = JsonScan.decN n := by
      rw [show uint.nat (W64 ((uint.nat i + ((JsonScan.decN n).length + 2) : Nat) : Int) - W64 1) -
          uint.nat (i + W64 1) = (JsonScan.decN n).length by word,
        show uint.nat (i + W64 1) = uint.nat i + 1 by word, ← List.drop_drop, hb]
      simp
    have hdl : 0 < (JsonScan.decN n).length := by rw [hdn]; simp
    wp_apply (wp_Digits b dq bs (i + W64 1) _ mx (by word) (by word)
      (by rw [hdg]; exact JsonScan.decN_digits n) (by rw [hdg, JsonScan.valD_decN]; exact hn)
     ) $$ Hs as Hs
    rw [hdg, JsonScan.valD_decN]
    simp only [Nat.add_assoc]
    iapply HΦ; iexact Hs
  all_goals
    have hdg : (bs.drop (uint.nat (i + W64 1))).take
        (uint.nat (W64 ((uint.nat i + ((JsonScan.decN n).length + 2) : Nat) : Int) - W64 1) -
          uint.nat (i + W64 1)) = JsonScan.decN n := by
      rw [show uint.nat (W64 ((uint.nat i + ((JsonScan.decN n).length + 2) : Nat) : Int) - W64 1) -
          uint.nat (i + W64 1) = (JsonScan.decN n).length by word,
        show uint.nat (i + W64 1) = uint.nat i + 1 by word, ← List.drop_drop, hb]
      simp
    have hdl : 0 < (JsonScan.decN n).length := by rw [hdn]; simp
    wp_apply (wp_Digits b dq bs (i + W64 1) _ mx (by word) (by word)
      (by rw [hdg]; exact JsonScan.decN_digits n) (by rw [hdg, JsonScan.valD_decN]; exact hn)
     ) $$ Hs as Hs
    rw [hdg, JsonScan.valD_decN]
    simp only [Nat.add_assoc]
    iapply HΦ; iexact Hs
end proof

end models_lab.jsoncodec
end Perennial
