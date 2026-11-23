/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/client/VarintPure.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The varint decoding the swift package's `readUvarint`/`readVarint` (copies of Go's
`encoding/binary`, change log C5') compute, as pure Lean, and its relation to `Wire.lean`'s
`uvarint`.
-/
module

public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.swift.Wire
public import Perennial.Std.Word

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

namespace sp

/-- The value of varint bytes (7 bits each, least significant first). -/
def uvDec : List w8 → Nat
  | [] => 0
  | b :: bs => b.toNat % 128 + 128 * uvDec bs

/-- Bytes `ReadUvarint` accepts: continuation bytes (high bit set), then a last byte (high bit
clear), at most 10 in all. -/
def uvTerm (d : List w8) : Prop :=
  ∃ (pre : List w8) (c : w8), d = pre ++ [c] ∧ (∀ b ∈ pre, 128 ≤ b.toNat) ∧ c.toNat < 128 ∧
    d.length ≤ 10

theorem uvDec_lt (l : List w8) : uvDec l < 128 ^ l.length := by
  induction l with
  | nil => simp [uvDec]
  | cons b bs ih =>
    simp only [uvDec, List.length_cons, Nat.pow_succ]
    have := Nat.mod_lt b.toNat (by decide : 128 > 0)
    have h : 128 * uvDec bs + 128 ≤ 128 ^ bs.length * 128 := by
      have := Nat.mul_le_mul_left 128 (Nat.succ_le_of_lt ih); rw [Nat.mul_comm] at this; omega
    omega

theorem uvDec_snoc (l : List w8) (b : w8) :
    uvDec (l ++ [b]) = uvDec l + 128 ^ l.length * (b.toNat % 128) := by
  induction l with
  | nil => simp [uvDec]
  | cons a rest ih =>
    simp only [List.cons_append, uvDec, ih, List.length_cons, Nat.pow_succ]
    rw [Nat.mul_add, Nat.mul_comm (128 ^ rest.length) 128, Nat.mul_assoc]; omega

theorem uvarint_shape (n : Nat) : ∃ (pre : List w8) (c : w8), uvarint n = pre ++ [c] ∧
    (∀ b ∈ pre, 128 ≤ b.toNat) ∧ c.toNat < 128 ∧ uvDec (uvarint n) = n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hn : n < 128
    · refine ⟨[], W8 n, ?_, by simp, ?_, ?_⟩
      · rw [uvarint, dif_pos hn]; rfl
      · simp [W8]; omega
      · rw [uvarint, dif_pos hn]; simp [uvDec, W8]; omega
    · obtain ⟨pre, c, h1, h2, h3, h4⟩ := ih (n / 128) (by omega)
      refine ⟨W8 (n % 128 + 128) :: pre, c, ?_, ?_, h3, ?_⟩
      · rw [uvarint, dif_neg hn, h1]; rfl
      · intro b hb
        rcases List.mem_cons.1 hb with rfl | hb
        · simp [W8]; omega
        · exact h2 b hb
      · rw [uvarint, dif_neg hn]
        simp only [uvDec]
        rw [h4]
        simp [W8]; omega

theorem uvarint_length (n k : Nat) (hk : 1 ≤ k) (h : n < 128 ^ k) : (uvarint n).length ≤ k := by
  induction k generalizing n with
  | zero => omega
  | succ k ih =>
    rw [uvarint]
    split
    · simp
    · rename_i hn
      simp only [List.length_cons]
      have : 1 ≤ k := by
        rcases Nat.eq_zero_or_pos k with h0 | h0
        · subst h0; simp at h; omega
        · exact h0
      have := ih (n / 128) this (by rw [Nat.pow_succ] at h; omega)
      omega

theorem uvarint_term (n : Nat) (h : n < 2 ^ 63) : uvTerm (uvarint n) ∧ uvDec (uvarint n) = n := by
  obtain ⟨pre, c, h1, h2, h3, h4⟩ := uvarint_shape n
  refine ⟨⟨pre, c, h1, h2, h3, uvarint_length n 10 (by decide) (by omega)⟩, h4⟩

/-- Accepted varints are prefix-free. -/
theorem uvTerm_prefix (d e x y : List w8) (hd : uvTerm d) (he : uvTerm e) (h : d ++ x = e ++ y) :
    d = e := by
  obtain ⟨p1, c1, rfl, hp1, hc1, -⟩ := hd
  obtain ⟨p2, c2, rfl, hp2, hc2, -⟩ := he
  induction p1 generalizing p2 with
  | nil =>
    cases p2 with
    | nil => simp at h ⊢; exact h.1
    | cons b p2 =>
      simp at h; have := hp2 b (by simp); rw [← h.1] at this; omega
  | cons a p1 ih =>
    cases p2 with
    | nil =>
      simp at h; have := hp1 a (by simp); rw [h.1] at this; omega
    | cons b p2 =>
      simp only [List.cons_append, List.cons.injEq] at h ⊢
      refine ⟨h.1, ?_⟩
      have := ih (fun z hz => hp1 z (List.mem_cons_of_mem _ hz)) p2 (by simpa using h.2)
        (fun z hz => hp2 z (List.mem_cons_of_mem _ hz))
      simpa using this

end sp

end Perennial.github_com.imdea_software.swiftpaxos
