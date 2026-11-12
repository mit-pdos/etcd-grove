/- Lean-first (no Rocq counterpart). The proof of `itoa`: the loop keeps `decDigits n₀ =
decDigits n ++ b` (each iteration prepends `n`'s last digit and divides `n` by ten). -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.itoa

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccrand

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.mvccrand

theorem decDigits_zero : decDigits 0 = [] := by
  rw [decDigits]; simp

theorem decDigits_pos (n : Nat) (h : n ≠ 0) :
    decDigits n = decDigits (n / 10) ++ [W8 (48 + n % 10 : Nat)] := by
  rw [decDigits]; simp [h]

theorem srem10 (m : w64) (h : 0 ≤ sint.Z m) : sint.Z (BitVec.srem m (W64 10)) = sint.Z m % 10 := by
  rw [show sint.Z (BitVec.srem m (W64 10)) = (BitVec.srem m (W64 10)).toInt from rfl,
    BitVec.toInt_srem, show (W64 10).toInt = 10 by decide, Int.tmod_eq_emod_of_nonneg h]

theorem sdiv10 (m : w64) (h : 0 ≤ sint.Z m) : sint.Z (BitVec.sdiv m (W64 10)) = sint.Z m / 10 := by
  rw [show sint.Z (BitVec.sdiv m (W64 10)) = (BitVec.sdiv m (W64 10)).toInt from rfl,
    BitVec.toInt_sdiv, show (W64 10).toInt = 10 by decide, Int.tdiv_eq_ediv_of_nonneg h]
  have h1 := BitVec.toInt_lt (x := m)
  have h2 : sint.Z m = m.toInt := rfl
  apply Int.bmod_eq_of_le <;> omega

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccrand.Assumptions]

theorem itoa.wp_proof : itoa.spec (GF := GF) (hG := hG) := by
  intro n hn
  wp_start
  wp_auto
  wp_if_destruct
  · (try wp_auto)
    rw [show itoaM (sint.nat (W64 0)) = go!"0" by rfl]
    iapply HΦ; itrivial
  · (try wp_auto)
    have hn0 : sint.nat n ≠ 0 := by intro h; apply Hif; word
    ihave HI : (∃ (m : w64) (b : GoSlice) (bs : GoString),
        "n" ∷ n_ptr ↦ m ∗ "b" ∷ b_ptr ↦ b ∗ "Hb" ∷ b ↦* bs ∗
        "%Hm" ∷ ⌜0 ≤ sint.Z m ∧ decDigits (sint.nat n) = decDigits (sint.nat m) ++ bs⌝ :
        IProp GF) $$ [n b]
    · iexists n, slice.nil, []
      iframe
      isplitl
      · iapply ownSlice_nil
      ipureintro; exact ⟨hn, by simp⟩
    wp_for HI
    by_cases Hlt : sint.Z (W64 0) < sint.Z m
    · -- an iteration
      rw [decide_eq_true Hlt]; simp only [↓reduceIte]
      (try wp_auto)
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %osl ⟨Hosl, Hcap⟩
      (try wp_auto)
      wp_apply wp_slice_append $$ [$Hosl $Hcap $Hb] as %b' ⟨Hb', -, -⟩
      (try wp_auto)
      wp_for_post
      iframe
      iexists _, b', _
      iframe
      ipureintro
      refine ⟨by
        have := sdiv10 m Hm.1
        generalize BitVec.sdiv m (W64 10) = r at this ⊢
        omega, ?_⟩
      rw [Hm.2, decDigits_pos (sint.nat m) (by word), List.append_assoc]
      have hr := srem10 m Hm.1
      have hd := sdiv10 m Hm.1
      have hm10 : sint.Z (W64 48 + BitVec.srem m (W64 10)) =
          ((48 + sint.nat m % 10 : Nat) : Int) := by
        generalize BitVec.srem m (W64 10) = r at hr ⊢
        have : sint.nat m = (sint.Z m).toNat := rfl
        word
      have hq : sint.nat (BitVec.sdiv m (W64 10)) = sint.nat m / 10 := by
        generalize BitVec.sdiv m (W64 10) = r at hd ⊢
        have h1 : sint.nat m = (sint.Z m).toNat := rfl
        have h2 : sint.nat r = (sint.Z r).toNat := rfl
        rw [h1, h2, hd]; omega
      rw [hm10, hq]
    · -- the loop's end
      rw [decide_eq_false Hlt]; simp only [Bool.false_eq_true, ↓reduceIte]
      have hm0 : sint.nat m = 0 := by word
      rw [hm0, decDigits_zero, List.nil_append] at Hm
      (try wp_auto)
      wp_apply wp_bytes_to_string b bs (DFrac.own 1) $$ [$Hb] as -
      (try wp_auto)
      unfold itoaM
      rw [ite_eq_right_iff.2 (fun h => absurd h hn0), Hm.2]
      iapply HΦ; itrivial

end proof

end mvccrand
end EtcdGrove
end Perennial
