/-
`jsoncodec.scanNumber` against `JsonScan.numL` (an internal function: `scanScalar` uses this
lemma). Ported from dsverify-lab's `examples/vr/proof/VsrProof/Proof/jsoncodec/GoNumber.lean`
(lab master 915f964).
-/
module

public import Net.Proof.models_lab.jsoncodec.ScanString

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.iris.style.nameCheck false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace models_lab.jsoncodec

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : models_lab.jsoncodec.Assumptions]

set_option goose.wp.extras true

set_option maxHeartbeats 4000000 in
/-- `scanNumber(b, i, eof)`. -/
theorem wp_scanNumber (b : GoSlice) (dq : DFrac) (bs : List w8) (i : w64) (eof : Bool)
    (hi : uint.nat i < bs.length) :
    {{ (b ↦*{dq} bs : IProp GF) }}
      (App (App (App (Val (@! models_lab.jsoncodec.scanNumber)) (Val #b)) (Val #i))
        (Val #eof))
    {{ RET (PairV #(W64 ((JsonScan.numL (bs.drop (uint.nat i)) (uint.nat i) eof).1 : Int))
          #(W64 ((JsonScan.numL (bs.drop (uint.nat i)) (uint.nat i) eof).2 : Int)));
        b ↦*{dq} bs }} := by
  wp_start as Hs
  ihave %Hlen := ownSlice_len $$ Hs
  have hl63 := len_lt b bs Hlen
  generalize hN : JsonScan.numL (bs.drop (uint.nat i)) (uint.nat i) eof = N
  simp only [models_lab.jsoncodec.Done, models_lab.jsoncodec.More,
    models_lab.jsoncodec.Bad]
  wp_auto
  ldidx i, c0, Hc0
  -- the sign
  wp_if_destruct
  rotate_left
  have hK : N = JsonScan.intL (bs.drop (uint.nat i)) (uint.nat i) eof := by
    rw [← hN]; exact JsonScan.numL_pos bs eof _ c0 Hc0 (by intro h; apply Hif; rw [h]; rfl)
  have hjl : uint.nat i < bs.length := hi
  generalize hjv : i = jv at hK hjl ⊢
  rotate_left
  have hneg := JsonScan.numL_neg bs eof _ (by rw [Hc0]; rfl)
  rw [hN] at hneg
  wp_if_destruct
  · have e : N = (1, uint.nat i + 1) := by
      rw [hneg, List.getElem?_eq_none (by word)]
    fin_ret e
  ldidx (i + W64 1), d, Hd
  wp_apply wp_isDigit d
  by_cases hdd : JsonScan.isDig d = false
  · simp only [hdd]
    wp_auto
    have e : N = (2, uint.nat i + 1) := by
      rw [hneg, show uint.nat i + 1 = uint.nat (i + W64 1) by word, Hd]; simp [hdd]
    fin_ret e
  simp only [Bool.not_eq_false] at hdd
  simp only [hdd]
  wp_auto
  have hK : N = JsonScan.intL (bs.drop (uint.nat (i + W64 1))) (uint.nat (i + W64 1)) eof := by
    rw [hneg, show uint.nat i + 1 = uint.nat (i + W64 1) by word, Hd]; simp [hdd]
  have hjl : uint.nat (i + W64 1) < bs.length := by word
  generalize hjv : i + W64 1 = jv at hK hjl ⊢
  -- the integer part
  all_goals
    ldidx jv, c1, Hc1
    wp_if_destruct
    have hK2 : N = JsonScan.fracL (bs.drop (uint.nat (jv + W64 1))) (uint.nat (jv + W64 1)) eof := by
      rw [hK, JsonScan.intL_zero bs eof _ (by rw [Hc1]; rfl),
        show uint.nat (jv + W64 1) = uint.nat jv + 1 by word]
    have hjl2 : uint.nat (jv + W64 1) ≤ bs.length := by word
    generalize hjv2 : jv + W64 1 = jv2 at hK2 hjl2 ⊢
    rotate_left
    wp_apply wp_scanDigits b dq bs jv (by omega) $$ Hs as Hs
    rw [JsonScan.digitsL_drop]
    have hde := digEnd_le bs (uint.nat jv) (by omega)
    have hdz : uint.nat (W64 (JsonScan.digEnd bs (uint.nat jv) : Int)) =
        JsonScan.digEnd bs (uint.nat jv) := by word
    have hK2 : N = JsonScan.fracL (bs.drop (uint.nat (W64 (JsonScan.digEnd bs (uint.nat jv) : Int))))
        (uint.nat (W64 (JsonScan.digEnd bs (uint.nat jv) : Int))) eof := by
      rw [hK, JsonScan.intL_dig bs eof _ c1 Hc1 (by intro h; apply Hif; rw [h]; rfl), hdz]
    have hjl2 : uint.nat (W64 (JsonScan.digEnd bs (uint.nat jv) : Int)) ≤ bs.length := by
      rw [hdz]; exact hde
    generalize hjv2 : W64 (JsonScan.digEnd bs (uint.nat jv) : Int) = jv2 at hK2 hjl2 ⊢
  -- the end after the integer part
  all_goals
    wp_if_destruct
    · have hend : bs.length ≤ uint.nat b.len := by word
      rw [JsonScan.fracL_end bs eof _ hend] at hK2
      wp_if_destruct
      · simp [JsonScan.endS] at hK2; fin_ret hK2
      · simp [JsonScan.endS] at hK2; fin_ret hK2
    have hjl3 : uint.nat jv2 < bs.length := by word
    -- the fraction
    ldidx jv2, c2, Hc2
    wp_if_destruct
    rotate_left
    have hK3 : N = JsonScan.expL (bs.drop (uint.nat jv2)) (uint.nat jv2) eof := by
      rw [hK2, JsonScan.fracL_nodot bs eof _ c2 Hc2 (by intro h; apply Hif; rw [h]; rfl)]
    have hjl4 : uint.nat jv2 < bs.length := hjl3
    generalize hjv3 : jv2 = jv3 at hK3 hjl4 ⊢
    rotate_left
    have hdot := JsonScan.fracL_dot bs eof _ (by rw [Hc2]; rfl)
    rw [hdot] at hK2
    wp_if_destruct
    · rw [List.getElem?_eq_none (by word)] at hK2
      fin_ret hK2
    ldidx (jv2 + W64 1), d2, Hd2
    rw [show uint.nat jv2 + 1 = uint.nat (jv2 + W64 1) by word, Hd2] at hK2
    wp_apply wp_isDigit d2
    by_cases hd2 : JsonScan.isDig d2 = false
    · simp only [hd2]
      wp_auto
      simp only [hd2, Bool.not_false, if_true, ite_true] at hK2
      fin_ret hK2
    simp only [Bool.not_eq_false] at hd2
    simp only [hd2]
    wp_auto
    simp only [hd2, Bool.not_true, Bool.false_eq_true, if_false, ite_false] at hK2
    wp_apply wp_scanDigits b dq bs (jv2 + W64 1) (by word) $$ Hs as Hs
    rw [JsonScan.digitsL_drop]
    have hde := digEnd_le bs (uint.nat (jv2 + W64 1)) (by word)
    have hdz : uint.nat (W64 (JsonScan.digEnd bs (uint.nat (jv2 + W64 1)) : Int)) =
        JsonScan.digEnd bs (uint.nat (jv2 + W64 1)) := by word
    wp_if_destruct
    · have hend : bs.length ≤ JsonScan.digEnd bs (uint.nat (jv2 + W64 1)) := by
        rw [← hdz]; word
      rw [JsonScan.expL_end bs eof _ hend] at hK2
      wp_if_destruct
      · simp [JsonScan.endS] at hK2; fin_ret hK2
      · simp [JsonScan.endS] at hK2; fin_ret hK2
    have hK3 : N = JsonScan.expL
        (bs.drop (uint.nat (W64 (JsonScan.digEnd bs (uint.nat (jv2 + W64 1)) : Int))))
        (uint.nat (W64 (JsonScan.digEnd bs (uint.nat (jv2 + W64 1)) : Int))) eof := by
      rw [hK2, hdz]
    have hjl4 : uint.nat (W64 (JsonScan.digEnd bs (uint.nat (jv2 + W64 1)) : Int)) < bs.length := by
      word
    generalize hjv3 : W64 (JsonScan.digEnd bs (uint.nat (jv2 + W64 1)) : Int) = jv3 at hK3 hjl4 ⊢
  -- the exponent
  all_goals
    ldidx jv3, c3, Hc3
    wp_if_destruct
    have hK4 := hK3
    rw [JsonScan.expL_e bs eof _ _ Hc3 (Or.inl rfl)] at hK4
    rotate_left
    have hn1 : ¬ c3 = W8 101 := Hif
    ldagain jv3, Hc3
    wp_if_destruct
    have hK4 := hK3
    rw [JsonScan.expL_e bs eof _ _ Hc3 (Or.inr rfl)] at hK4
    rotate_left
    · rw [JsonScan.expL_noe bs eof _ c3 Hc3 (by
        rintro (h | h)
        · apply hn1; rw [h]; rfl
        · apply Hif; rw [h]; rfl)] at hK3
      fin_ret hK3
  -- after `e`: the sign
  all_goals
    wp_if_destruct
    rotate_left
    rw [List.getElem?_eq_none (by word)] at hK4
    simp only at hK4
    rw [show uint.nat jv3 + 1 = uint.nat (jv3 + W64 1) by word] at hK4
    have hjEl : uint.nat (jv3 + W64 1) ≤ bs.length := by word
    generalize hjE : jv3 + W64 1 = jE at hK4 hjEl ⊢
    rotate_left
    ldidx (jv3 + W64 1), sg, Hsg
    rw [show uint.nat jv3 + 1 = uint.nat (jv3 + W64 1) by word, Hsg] at hK4
    simp only at hK4
    wp_if_destruct
    rw [if_pos (by decide), show uint.nat jv3 + 2 = uint.nat (jv3 + W64 1 + W64 1) by word] at hK4
    have hjEl : uint.nat (jv3 + W64 1 + W64 1) ≤ bs.length := by word
    generalize hjE : jv3 + W64 1 + W64 1 = jE at hK4 hjEl ⊢
    rotate_left
    have hn43 : ¬ sg = W8 43 := Hif
    ldagain (jv3 + W64 1), Hsg
    wp_if_destruct
    rw [if_pos (by decide), show uint.nat jv3 + 2 = uint.nat (jv3 + W64 1 + W64 1) by word] at hK4
    have hjEl : uint.nat (jv3 + W64 1 + W64 1) ≤ bs.length := by word
    generalize hjE : jv3 + W64 1 + W64 1 = jE at hK4 hjEl ⊢
    rotate_left
    have hn45 : ¬ sg = W8 45 := Hif
    rw [if_neg (by
      rintro (h | h)
      · apply hn43; rw [h]; rfl
      · apply hn45; rw [h]; rfl)] at hK4
    have hjEl : uint.nat (jv3 + W64 1) ≤ bs.length := by word
    generalize hjE : jv3 + W64 1 = jE at hK4 hjEl ⊢
  -- the exponent's digits
  all_goals
    unfold JsonScan.expAt at hK4
    wp_if_destruct
    · rw [show uint.nat b.len = bs.length by word, List.getElem?_eq_none (Nat.le_refl _)] at hK4
      simp only at hK4
      fin_ret hK4
    have hjE' : uint.nat jE < bs.length := by word
    ldidx jE, d3, Hd3
    rw [Hd3] at hK4
    simp only at hK4
    wp_apply wp_isDigit d3
    by_cases hd3 : JsonScan.isDig d3 = false
    · simp only [hd3]
      wp_auto
      simp only [hd3, Bool.not_false, if_true, ite_true] at hK4
      fin_ret hK4
    simp only [Bool.not_eq_false] at hd3
    simp only [hd3]
    wp_auto
    simp only [hd3, Bool.not_true, Bool.false_eq_true, if_false, ite_false] at hK4
    wp_apply wp_scanDigits b dq bs jE (by omega) $$ Hs as Hs
    rw [JsonScan.digitsL_drop]
    have hde := digEnd_le bs (uint.nat jE) (by omega)
    wp_if_destruct
    · have hend : bs.length ≤ JsonScan.digEnd bs (uint.nat jE) := by word
      rw [if_pos hend] at hK4
      wp_if_destruct
      · simp [JsonScan.endS] at hK4; fin_ret hK4
      · simp [JsonScan.endS] at hK4; fin_ret hK4
    · have hend : ¬ bs.length ≤ JsonScan.digEnd bs (uint.nat jE) := by word
      rw [if_neg hend] at hK4
      fin_ret hK4

end spec


end models_lab.jsoncodec
end Perennial
