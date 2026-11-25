/-
The proof of `jsoncodec.Uint` (`Net/Spec/models_lab/jsoncodec/Uint.lean`). Ported from dsverify-lab's `wp_Uint` (`examples/vr/proof/VsrProof/Proof/jsoncodec/GoDec.lean`,
lab master 915f964).
-/
module

public import Net.Spec.models_lab.jsoncodec.Uint
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

theorem Uint.wp_proof (wp_At : At.spec (GF := GF) (hG := hG)) (wp_ValueEnd : ValueEnd.spec (GF := GF) (hG := hG)) (wp_Digits : Digits.spec (GF := GF) (hG := hG)) :
    Uint.spec (GF := GF) (hG := hG) := by
  intro b dq bs i mx n c rest hc hb hn
  wp_start as Hs
  ihave %Hlen := ownSlice_len $$ Hs
  have hl63 := len_lt b bs Hlen
  have hlen : uint.nat i + (JsonScan.decN n).length + 1 ≤ bs.length := by
    have := congrArg List.length hb; simp at this; omega
  obtain ⟨d, ds, hdn⟩ : ∃ d ds, JsonScan.decN n = d :: ds := by
    cases h : JsonScan.decN n with
    | nil => exact absurd h (JsonScan.decN_ne_nil n)
    | cons d ds => exact ⟨d, ds, rfl⟩
  have hdd : JsonScan.isDig d = true := JsonScan.decN_digits n d (by rw [hdn]; simp)
  have h0 : bs[uint.nat i]? = some d := by
    have := congrArg (fun l => l[0]?) hb; simp only [List.getElem?_drop] at this; simpa [hdn] using this
  have hsk : JsonScan.skipEnd bs (uint.nat i) = uint.nat i :=
    skipEnd_ns' bs _ d h0 (JsonScan.isDig_ne d hdd).1
  simp only [models_lab.jsoncodec.Set', models_lab.jsoncodec.Keep,
    models_lab.jsoncodec.TypeErr]
  wp_auto
  wp_apply (wp_At b dq bs i d (by omega) (by rw [hsk]; exact h0)) $$ Hs as Hs
  rw [hsk, show W64 ((uint.nat i : Nat) : Int) = i by word]
  have hsc : JsonScan.scanL (bs.drop (uint.nat i)) true = (0, (JsonScan.decN n).length) := by
    rw [hb]; exact JsonScan.scanL_num n c rest hc
  wp_apply (wp_ValueEnd b dq bs i (by omega) (by rw [hsc])) $$ Hs as Hs
  rw [hsc]
  simp only
  have hd110 : d ≠ W8 110 := by
    intro h; subst h; exact absurd hdd (by decide)
  simp only [hd110, decide_false]
  wp_auto
  wp_apply wp_isDigit d
  simp only [hdd]
  wp_auto
  have hdg : (bs.drop (uint.nat i)).take
      (uint.nat (W64 ((uint.nat i + (JsonScan.decN n).length : Nat) : Int)) - uint.nat i) =
      JsonScan.decN n := by
    rw [show uint.nat (W64 ((uint.nat i + (JsonScan.decN n).length : Nat) : Int)) - uint.nat i =
      (JsonScan.decN n).length by word, hb]
    simp
  wp_apply (wp_Digits b dq bs i _ mx (by rw [hdn] at hlen ⊢; simp at hlen ⊢; word) (by word)
    (by rw [hdg]; exact JsonScan.decN_digits n) (by rw [hdg, JsonScan.valD_decN]; exact hn)) $$ Hs as Hs
  rw [hdg, JsonScan.valD_decN]
  iapply HΦ; iexact Hs
end proof

end models_lab.jsoncodec
end Perennial
