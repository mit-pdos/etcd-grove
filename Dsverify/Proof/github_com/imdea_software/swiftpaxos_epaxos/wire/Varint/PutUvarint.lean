module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Interface.Varint

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.imdea_software.swiftpaxos_epaxos.kvs model

attribute [local instance] GooseGlobalGS.gooseInvGS

theorem uvarintEnc_length_pos (n : Nat) : 0 < (uvarintEnc n).length := by
  rw [uvarintEnc.eq_1]; split <;> simp

theorem uvarintEnc_ge (n : Nat) (h : 128 ≤ n) :
    uvarintEnc n = W8 (n % 128 + 128) :: uvarintEnc (n / 128) := by
  rw [uvarintEnc.eq_1]; simp [show ¬ n < 128 by omega]

theorem byte_or_key : ∀ a : BitVec 8, a ||| 128 = BitVec.ofNat 8 (a.toNat % 128 + 128) := by
  decide

/-- `byte(x) | 0x80`. -/
theorem byte_or_128 (xv : w64) :
    W8 (uint.Z xv) ||| W8 128 = W8 ((xv.toNat : Int) % 128 + 128) := by
  have h1 : W8 (uint.Z xv) = BitVec.ofNat 8 xv.toNat := by
    apply BitVec.eq_of_toNat_eq; simp [W8, uint.Z]
  have h2 : W8 ((xv.toNat : Int) % 128 + 128) = BitVec.ofNat 8 (xv.toNat % 128 + 128) := by
    apply BitVec.eq_of_toNat_eq; simp [W8]; omega
  rw [h1, h2, show W8 128 = 128 from rfl, byte_or_key]
  congr 1; simp

/-- Storing `c` at index `pre.length` of `pre ++ bs.drop pre.length`. -/
theorem set_after_prefix (pre bs : List w8) (c : w8) (h : pre.length < bs.length) :
    (pre ++ bs.drop pre.length).set pre.length c = (pre ++ [c]) ++ bs.drop (pre ++ [c]).length := by
  rw [List.set_append_right _ _ (Nat.le_refl _), Nat.sub_self]
  obtain ⟨d, rest, hd⟩ : ∃ d rest, bs.drop pre.length = d :: rest := by
    cases h' : bs.drop pre.length with
    | nil => simp at h'; omega
    | cons d rest => exact ⟨d, rest, rfl⟩
  rw [hd]
  have : bs.drop (pre ++ [c]).length = rest := by
    simp only [List.length_append, List.length_singleton]
    rw [← List.drop_drop, hd]; rfl
  rw [this]; simp

theorem uvarintEnc_lt (n : Nat) (h : n < 128) : uvarintEnc n = [W8 n] := by
  rw [uvarintEnc.eq_1]; simp [h]

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [epaxos.Assumptions]

set_option goose.wp.extras true

theorem epaxos.putUvarint.spec_holds (buf : GoSlice) (bs : List w8) (x : w64) :
  {{ pkgInit_epaxos (GF := GF) ∗ ⌜(uvarintEnc x.toNat).length ≤ bs.length⌝ ∗ buf ↦* bs }}
    (App (App (Val (@! epaxos.putUvarint)) (Val #buf)) (Val #x))
  {{ RET #(W64 (uvarintEnc x.toNat).length);
      buf ↦* (uvarintEnc x.toNat ++ bs.drop (uvarintEnc x.toNat).length) }} := by
  wp_start as ⟨%Hl, Hb⟩
  ihave %Hbl := ownSlice_len _ _ _ $$ Hb
  have hbl : (bs.length : Int) = sint.Z buf.len := by
    rw [Hbl.1]; exact Int.toNat_of_nonneg Hbl.2
  have h63 : sint.Z buf.len < 2 ^ 63 := by word
  clear Hbl
  wp_auto
  ihave HL : (∃ (pre : List w8) (xv : w64),
      "x" ∷ x_ptr ↦ xv ∗ "i" ∷ i_ptr ↦ W64 pre.length ∗
      "Hb" ∷ buf ↦* (pre ++ bs.drop pre.length) ∗
      "%Hinv" ∷ ⌜pre ++ uvarintEnc xv.toNat = uvarintEnc x.toNat⌝ : IProp GF) $$ [x i Hb]
  · iexists [], x
    simp only [List.length_nil, List.drop_zero, List.nil_append]
    iframe x i Hb
  wp_for HL
  have hE := uvarintEnc_length_pos xv.toNat
  have hlen : pre.length + (uvarintEnc xv.toNat).length = (uvarintEnc x.toNat).length := by
    rw [← Hinv, List.length_append]
  wp_if_destruct
  · -- `x ≥ 0x80`
    have hx : 128 ≤ xv.toNat := by simp at Hif; word
    rw [uvarintEnc_ge _ hx] at Hinv
    have hl1 : pre.length < bs.length := by omega
    have hpZ : sint.Z (W64 (pre.length : Int)) = pre.length := sint_Z_W64_length (by omega)
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, by omega⟩)]
    rw [byte_or_128]
    wp_apply wp_store_slice_index buf _ _ _ $$ [$Hb] as Hb
    · ipureintro; rw [hpZ]; simp; omega
    rw [hpZ, Int.toNat_natCast, set_after_prefix _ _ _ hl1]
    wp_for_post
    have hi : W64 (pre.length : Int) + W64 1 = W64 ((pre ++ [W8 ((xv.toNat : Int) % 128 + 128)]).length : Int) := by
      simp only [List.length_append, List.length_singleton]; push_cast; word
    rw [hi]
    iframe
    iexists _, xv >>> W64 7
    iframe x i Hb
    ipureintro
    rw [List.append_assoc, List.singleton_append, show (xv >>> W64 7).toNat = xv.toNat / 128 by
      simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]]
    exact Hinv
  -- the last byte
  have hx : xv.toNat < 128 := by simp at Hif; word
  rw [uvarintEnc_lt _ hx] at Hinv
  have hl1 : pre.length < bs.length := by omega
  have hpZ : sint.Z (W64 (pre.length : Int)) = pre.length := sint_Z_W64_length (by omega)
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, by omega⟩)]
  wp_apply wp_store_slice_index buf _ _ _ $$ [$Hb] as Hb
  · ipureintro; rw [hpZ]; simp; omega
  rw [hpZ, Int.toNat_natCast, set_after_prefix _ _ _ hl1]
  have hu : uint.Z xv = (xv.toNat : Int) := rfl
  rw [hu, ← Hinv]
  have hi : W64 (pre.length : Int) + W64 1 = W64 ((pre ++ [W8 (xv.toNat : Int)]).length : Int) := by
    simp only [List.length_append, List.length_singleton]; push_cast; word
  rw [hi]
  iapply HΦ $$ Hb

end heap
end Perennial.github_com.imdea_software.swiftpaxos_epaxos
