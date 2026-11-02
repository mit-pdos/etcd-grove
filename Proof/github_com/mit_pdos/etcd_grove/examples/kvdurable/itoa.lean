/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvdurable/itoa.lean`. Lean-first
(no Rocq counterpart).

The loop prepends `n`'s last digit and divides `n` by ten; the invariant: the digits still to come,
then the bytes so far, are `N`'s (`decimalB_step`: `Nat.toDigits_eq_ite`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.itoa

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvdurable

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

private theorem digitChar_toNat (d : Nat) (h : d < 10) : (Nat.digitChar d).toNat = 48 + d := by
  match d, h with
  | 0, _ => rw [Nat.digitChar_eq_zero.2 rfl]; rfl
  | 1, _ => rw [Nat.digitChar_eq_one.2 rfl]; rfl
  | 2, _ => rw [Nat.digitChar_eq_two.2 rfl]; rfl
  | 3, _ => rw [Nat.digitChar_eq_three.2 rfl]; rfl
  | 4, _ => rw [Nat.digitChar_eq_four.2 rfl]; rfl
  | 5, _ => rw [Nat.digitChar_eq_five.2 rfl]; rfl
  | 6, _ => rw [Nat.digitChar_eq_six.2 rfl]; rfl
  | 7, _ => rw [Nat.digitChar_eq_seven.2 rfl]; rfl
  | 8, _ => rw [Nat.digitChar_eq_eight.2 rfl]; rfl
  | 9, _ => rw [Nat.digitChar_eq_nine.2 rfl]; rfl
  | _ + 10, h => exact absurd h (by omega)

/-- A nonzero `m`'s digits: those of `m / 10` (none if `m < 10`), then its last digit. -/
private theorem decimalB_step (m : Nat) :
    decimalB m = (if m < 10 then [] else decimalB (m / 10)) ++ [W8 ((48 + m % 10 : Nat) : Int)] := by
  unfold decimalB
  rw [Nat.toDigits_eq_ite (by decide)]
  split
  · rename_i h
    simp only [List.map_cons, List.map_nil, List.nil_append, Nat.mod_eq_of_lt h,
      digitChar_toNat m h]
  · simp only [List.map_append, List.map_cons, List.map_nil,
      digitChar_toNat (m % 10) (Nat.mod_lt _ (by decide))]

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt durableExt]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvdurable.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [AllG GF] [KdStor GF]

attribute [local instance] kdStorageModel

theorem itoa.wp_proof : itoa.spec (GF := GF) (hG := hG) := by
  intro N
  wp_start as #Hpkg
  wp_auto
  wp_if_destruct
  · have h0 : decimalB (uint.nat (W64 0)) = [W8 48] := by rw [decimalB_step]; rfl
    rw [show go!"0" = decimalB (uint.nat (W64 0)) by rw [h0]; rfl]
    iapply HΦ
    itrivial
  · ihave IH : iprop(∃ (k : w64) (bsl : GoSlice) (bs : List w8),
        "n" ∷ n_ptr ↦ k ∗ "b" ∷ b_ptr ↦ bsl ∗ "Hb" ∷ bsl ↦* bs ∗
        "Hbc" ∷ ownSliceCap w8 bsl (DFrac.own 1) ∗
        "%Hinv" ∷ ⌜(k = W64 0 ∧ bs = decimalB (uint.nat N)) ∨
          (k ≠ W64 0 ∧ decimalB (uint.nat N) = decimalB (uint.nat k) ++ bs)⌝) $$ [n b]
    · iexists N, slice.nil, []
      iframe n b
      isplitl
      · iapply ownSlice_nil
      isplitl
      · iapply ownSliceCap_nil
      ipureintro
      right
      exact ⟨Hif, by simp⟩
    wp_for IH
    wp_if_destruct
    · wp_apply wp_slice_literal (V := w8) [W8 (uint.Z (W64 48 + k % W64 10))]
      isplitr
      · ipureintro; rfl
      iintro %lp ⟨Hl, Hlc⟩
      wp_auto
      wp_apply wp_slice_append _ _ bsl bs (DFrac.own 1) $$ [$Hl $Hlc $Hb] as %s' ⟨Hs', Hc', -⟩
      wp_for_post
      iframe
      iexists _, s', _
      iframe
      ipureintro
      have Hk : k ≠ W64 0 := by
        intro h; subst h; simp only [decide_true] at Hif; exact absurd (intoVal_eq_iff.1 Hif) (by decide)
      have Hd : W8 (uint.Z (W64 48 + k % W64 10)) = W8 ((48 + uint.nat k % 10 : Nat) : Int) := by
        congr 1; word
      have Hdiv : uint.nat (k / W64 10) = uint.nat k / 10 := by word
      rcases Hinv with ⟨Hk0, -⟩ | ⟨-, Hinv⟩
      · exact absurd Hk0 Hk
      rw [Hinv, Hdiv, decimalB_step (uint.nat k), Hd]
      by_cases h10 : uint.nat k < 10
      · left; refine ⟨by word, ?_⟩; simp [h10]
      · right; refine ⟨by word, ?_⟩; simp [h10]
    · have Hk : k = W64 0 := by
        by_cases h : k = W64 0
        · exact h
        · exfalso; apply Hif; simp only [h, decide_false]; rfl
      subst Hk
      simp only [decide_true]
      simp only [Bool.not_true, decide_True_any, ↓reduceIte]
      wp_auto
      wp_apply wp_bytes_to_string bsl bs (DFrac.own 1) $$ Hb as Hb
      rcases Hinv with ⟨-, Hbs⟩ | ⟨Hne, -⟩
      · subst Hbs
        iapply HΦ
        itrivial
      · exact absurd rfl Hne

end proof

end kvdurable
end EtcdGrove
end Perennial
