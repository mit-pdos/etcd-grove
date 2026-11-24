/-
The proof of `jsoncodec.AppendUint` (`Net/Spec/models_lab/jsoncodec/AppendUint.lean`): the digits
written backwards into an array, then appended. Ported from dsverify-lab's `wp_AppendUint`
(`examples/vr/proof/VsrProof/Proof/jsoncodec/GoEnc.lean`, lab master 915f964).
-/
module

public import Net.Spec.models_lab.jsoncodec.AppendUint
public import Net.Proof.models_lab.jsoncodec.ScanString

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.iris.style.nameCheck false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace models_lab.jsoncodec

theorem decN_len_le (k n : Nat) (hk : 1 ≤ k) (h : n < 10 ^ k) : (JsonScan.decN n).length ≤ k := by
  induction k generalizing n with
  | zero => omega
  | succ k ih =>
    rw [JsonScan.decN_eq]
    split
    · simp only [List.length_singleton]; omega
    · rename_i hn
      have hk1 : 1 ≤ k := by
        rcases Nat.eq_zero_or_pos k with h0 | h0
        · subst h0; simp at h; omega
        · omega
      have := ih (n / 10) hk1 (by rw [Nat.pow_succ] at h; omega)
      simp; omega

theorem decN_len64 (n : Nat) (h : n < 2 ^ 64) : (JsonScan.decN n).length ≤ 20 :=
  decN_len_le 20 n (by omega) (by omega)

theorem decN_len_pos (n : Nat) : 1 ≤ (JsonScan.decN n).length := by
  have := JsonScan.decN_ne_nil n
  cases h : JsonScan.decN n with
  | nil => exact absurd h this
  | cons _ _ => simp

theorem list_set_drop {A : Type} (l : List A) (i : Nat) (c : A) (h : i < l.length) :
    (l.set i c).drop i = c :: l.drop (i + 1) := by
  induction l generalizing i with
  | nil => simp at h
  | cons a l ih =>
    cases i with
    | zero => simp
    | succ i => simp only [List.set_cons_succ, List.drop_succ_cons]; exact ih i (by simp at h; omega)


/-! ## `AppendCompact` on the codec's output -/

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : models_lab.jsoncodec.Assumptions]

set_option goose.wp.extras true
set_option maxHeartbeats 2000000

theorem AppendUint.wp_proof : AppendUint.spec (GF := GF) (hG := hG) := by
  intro b bs x
  wp_start as ⟨Hb, Hcap⟩
  wp_auto
  have hx := decN_len64 (uint.nat x) (by word)
  ihave IH : iprop(∃ (nn y : w64) (arr : List w8),
      "n" ∷ n_ptr ↦ nn ∗ "y" ∷ y_ptr ↦ y ∗
      "digits" ∷ digits_ptr ↦ (array.mk 20 arr : GoArray w8 20) ∗
      "%Hi" ∷ ⌜arr.length = 20 ∧ uint.nat nn ≤ 19 ∧ (0 < uint.nat y ∨ uint.nat nn = 0) ∧
        JsonScan.decN (uint.nat x) = JsonScan.decN (uint.nat y) ++ arr.drop (20 - uint.nat nn) ∧
        (arr.drop (20 - uint.nat nn)).length = uint.nat nn⌝) $$ [n y digits]
  · iexists _, _, _
    iframe
    ipureintro
    refine ⟨rfl, by simp, by simp, by simp <;> decide, by simp <;> decide⟩
  wp_for IH
  obtain ⟨hlen, hn19, hy, hdec, hdl⟩ := Hi
  rw [if_pos (by word)]
  wp_auto
  have hk : (sint.Z (W64 19 - nn)).toNat = 19 - uint.nat nn := by word
  obtain ⟨c0, hc0⟩ : ∃ c0, arr[19 - uint.nat nn]? = some c0 :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  icases array_acc (GF := GF) _ (sint.Z (W64 19 - nn)) _ _ (array.mk 20 arr) c0 (by word)
    (by rw [hk]; exact hc0) $$ digits with ⟨Hd, digits⟩
  wp_auto
  ihave digits := digits $$ Hd
  rw [hk]
  have hc : W8 (uint.Z (W64 48 + y % W64 10)) = BitVec.ofNat 8 (48 + uint.nat y % 10) := by
    word
  rw [hc]
  have hsd := list_set_drop arr (19 - uint.nat nn) (BitVec.ofNat 8 (48 + uint.nat y % 10)) (by omega)
  rw [show 19 - uint.nat nn + 1 = 20 - uint.nat nn by omega] at hsd
  wp_if_destruct
  · wp_for_post
    have hy10 : uint.nat y < 10 := by word
    have hfin : (arr.set (19 - uint.nat nn) (BitVec.ofNat 8 (48 + uint.nat y % 10))).drop
        (19 - uint.nat nn) = JsonScan.decN (uint.nat x) := by
      rw [hsd, hdec, JsonScan.decN_eq]; simp [hy10, Nat.mod_eq_of_lt hy10]
    rw [if_pos (by word)]
    icases (array_split (GF := GF) (W64 20 - (nn + W64 1)) digits_ptr _ 20
      (array.mk 20 (arr.set (19 - uint.nat nn) (BitVec.ofNat 8 (48 + uint.nat y % 10))))
      (by word)).1 $$ digits with ⟨D1, D2⟩
    ihave Hsl := slice_array (GF := GF) _ _ _ (by simp; omega) $$ D2
    rw [show W64 20 - (W64 20 - (nn + W64 1)) = W64 (20 - sint.Z (W64 20 - (nn + W64 1))) by word]
    wp_auto
    wp_apply wp_slice_append (V := w8) _ _ _ _ _ $$ [$Hb $Hcap $Hsl] as %b' ⟨Hb', Hcap', -⟩
    rw [show sint.nat (W64 20 - (nn + W64 1)) = 19 - uint.nat nn by word, hfin]
    iapply HΦ
    iframe
  · wp_for_post
    iframe
    iexists _, _, _
    iframe
    ipureintro
    have hy10 : 10 ≤ uint.nat y := by word
    have hd := JsonScan.decN_eq (uint.nat y)
    rw [if_neg (by omega)] at hd
    have e1 : uint.nat (nn + W64 1) = uint.nat nn + 1 := by word
    have e2 : uint.nat (y / W64 10) = uint.nat y / 10 := by word
    rw [e1, e2, show 20 - (uint.nat nn + 1) = 19 - uint.nat nn by omega, hsd]
    have hp := decN_len_pos (uint.nat y / 10)
    have hdx := congrArg List.length hdec
    rw [hd] at hdec hdx
    simp only [List.length_append, List.length_singleton] at hdx
    refine ⟨by simp [hlen], by omega, Or.inl (by omega), by rw [hdec]; simp, by simp [hdl]⟩
end proof

end models_lab.jsoncodec
end Perennial
