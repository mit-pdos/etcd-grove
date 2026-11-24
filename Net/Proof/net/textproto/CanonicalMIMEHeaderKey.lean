/-
The proof of `textproto.CanonicalMIMEHeaderKey` (`Net/Spec/net/textproto/CanonicalMIMEHeaderKey.lean`):
the quick check's loop, on a key it accepts as it is. `validHeaderFieldByte` (the 128-bit mask
test) is proved here (`wp_validHeaderFieldByte`): it is `fieldByte`.
-/
module

public import Net.Spec.net.textproto.CanonicalMIMEHeaderKey
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.perennial.goose.model.strings (wp_string_len)

namespace net.textproto

theorem fieldByte_mask_nat : ∀ n, n < 256 →
    (!decide (W64 1 <<< W64 (uint.Z (BitVec.ofNat 8 n)) &&& W64 288068722172624896 |||
        W64 1 <<< W64 (uint.Z (BitVec.ofNat 8 n - W8 64)) &&& W64 6341068274398134270 = W64 0)) =
      net.http.fieldByte (BitVec.ofNat 8 n) := by
  decide +kernel

theorem fieldByte_mask (c : w8) :
    (!decide (W64 1 <<< W64 (uint.Z c) &&& W64 288068722172624896 |||
        W64 1 <<< W64 (uint.Z (c - W8 64)) &&& W64 6341068274398134270 = W64 0)) =
      net.http.fieldByte c := by
  have h := fieldByte_mask_nat c.toNat c.isLt
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq] at h
  exact h

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.textproto.Assumptions]

theorem wp_validHeaderFieldByte (c : w8) :
    {{ (True : IProp GF) }}
      (App (Val (@! net.textproto.validHeaderFieldByte)) (Val #c))
    {{ RET #(net.http.fieldByte c); True }} := by
  wp_start
  wp_auto
  rw [fieldByte_mask]
  iapply HΦ; itrivial

theorem sintZ_len (n : Nat) (h : n < 2 ^ 63) : sint.Z (W64 (n : Int)) = n := by word

theorem w64_step (i : w64) (n : Nat) (h0 : 0 ≤ sint.Z i) (hlt : sint.Z i < sint.Z (W64 (n : Int)))
    (hn : n < 2 ^ 63) :
    sint.nat i < n ∧ 0 ≤ sint.Z (i + W64 1) ∧ sint.nat (i + W64 1) = sint.nat i + 1 := by
  have := sintZ_len n hn
  refine ⟨by word, by word, by word⟩

theorem canon_step (s : List w8) (i : Nat) (c : w8) (u : Bool) (h : s[i]? = some c) :
    net.http.canonQuickFrom (s.drop i) u =
      (if net.http.fieldByte c = false then true
       else if u = true ∧ 97 ≤ c.toNat ∧ c.toNat ≤ 122 then false
       else if u = false ∧ 65 ≤ c.toNat ∧ c.toNat ≤ 90 then false
       else net.http.canonQuickFrom (s.drop (i + 1)) (decide (c = W8 45))) := by
  have hi : i < s.length := by
    rcases Nat.lt_or_ge i s.length with hi | hi
    · exact hi
    · rw [List.getElem?_eq_none hi] at h; cases h
  rw [List.drop_eq_getElem_cons hi]
  rw [List.getElem?_eq_getElem hi] at h
  cases h
  rfl

theorem CanonicalMIMEHeaderKey.wp_proof :
    CanonicalMIMEHeaderKey.spec (GF := GF) (hG := hG) := by
  intro s
  wp_start as %Hq
  wp_auto
  ihave HI : (∃ (i : w64) (u : Bool), "i" ∷ i_ptr ↦ i ∗ "upper" ∷ upper_ptr ↦ u ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.nat i ≤ s.length ∧
        net.http.canonQuickFrom (s.drop (sint.nat i)) u = true⌝ : IProp GF) $$ [i upper]
  · iexists W64 0, true
    iframe
    ipureintro
    exact ⟨by word, by word, Hq⟩
  wp_for HI
  wp_apply wp_string_len as %Hl
  have hlen := sintZ_len _ Hl
  by_cases hlt : sint.Z i < sint.Z (W64 (s.length : Int))
  · simp only [hlt, _root_.decide_true, false_neq_true, true_neq_false, ↓reduceIte]
    obtain ⟨hi, hz, hn⟩ := w64_step i s.length Hi.1 hlt Hl
    clear hlt hlen
    obtain ⟨x, hx⟩ : ∃ x, s[sint.nat i]? = some x := ⟨_, List.getElem?_eq_getElem hi⟩
    wp_auto
    rw [ite_eq_left_of_eq_true _ _ (eq_true Hi.1), hx]
    wp_auto
    wp_apply wp_validHeaderFieldByte
    have hstep := canon_step s (sint.nat i) x u hx
    rw [Hi.2.2] at hstep
    by_cases hf : net.http.fieldByte x = false
    · rw [hf]
      wp_auto
      wp_for_post
      iapply HΦ; itrivial
    · have hf' : net.http.fieldByte x = true := by simpa using hf
      rw [hf']
      simp only [hf, Bool.true_eq_false, ↓reduceIte] at hstep
      wp_auto
      have hxz : uint.Z x = (x.toNat : Int) := rfl
      have e65 : uint.Z (W8 65) = 65 := rfl
      have e90 : uint.Z (W8 90) = 90 := rfl
      have e97 : uint.Z (W8 97) = 97 := rfl
      have e122 : uint.Z (W8 122) = 122 := rfl
      cases u
      all_goals
        repeat (first | wp_if_destruct | wp_auto)
      all_goals
        repeat' (split at hstep)
      all_goals first
        | (exfalso; simp only [e65, e90, e97, e122, hxz, Bool.false_eq_true, _root_.false_and,
            _root_.true_and] at *; omega)
        | (exfalso; cases hstep)
        | (wp_for_post
           iframe
           iexists _, _
           iframe
           ipureintro
           rw [hn]
           exact ⟨hz, by omega, hstep.symm⟩)

  · simp only [hlt, false_neq_true, true_neq_false, _root_.decide_false, _root_.decide_true,
      Bool.false_eq_true, ↓reduceIte]
    wp_auto
    iapply HΦ; itrivial

end proof

end net.textproto
end Perennial
