/-
Facts about 64-bit words that bbolt's arithmetic needs: `1 << n`, and signed remainder and
division (`%`, `/` on `int64`) of nonnegative operands.
-/
module

public import Perennial.Golang.Theory.Pre

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace bbolt

theorem shl_one_toNat (n : w64) (h : n.toNat ≤ 30) : (W64 1 <<< n).toNat = 2 ^ n.toNat := by
  rw [BitVec.shiftLeft_eq', BitVec.toNat_shiftLeft]
  have h1 : (W64 1).toNat = 1 := rfl
  rw [h1, Nat.shiftLeft_eq, Nat.one_mul]
  apply Nat.mod_eq_of_lt
  calc 2 ^ n.toNat ≤ 2 ^ 30 := Nat.pow_le_pow_right (by decide) h
    _ < 2 ^ 64 := by decide

theorem shl_one_sint (n : w64) (h : uint.Z n ≤ 30) :
    sint.Z (W64 1 <<< n) = 2 ^ n.toNat := by
  have hn : n.toNat ≤ 30 := by unfold uint.Z at h; omega
  have ht := shl_one_toNat n hn
  have hlt : 2 ^ n.toNat ≤ 2 ^ 30 := Nat.pow_le_pow_right (by decide) hn
  have : uint.Z (W64 1 <<< n) = 2 ^ n.toNat := by
    unfold uint.Z; rw [ht]; push_cast; rfl
  rw [← this]
  word


theorem msb_false_of_sint_nonneg (a : w64) (ha : 0 ≤ sint.Z a) : a.msb = false := by
  have : uint.Z a < 2 ^ 63 := by word
  rw [BitVec.msb_eq_decide]
  simp only [decide_eq_false_iff_not, Nat.not_le]
  unfold uint.Z at this
  omega

theorem sint_srem (a b : w64) (ha : 0 ≤ sint.Z a) (hb : 0 < sint.Z b) :
    sint.Z (BitVec.srem a b) = sint.Z a % sint.Z b := by
  have h1 := msb_false_of_sint_nonneg a ha
  have h2 := msb_false_of_sint_nonneg b (by omega)
  have hu : BitVec.srem a b = a % b := by
    unfold BitVec.srem; rw [h1, h2]; rfl
  rw [hu]
  have hmod : uint.Z (a % b) = uint.Z a % uint.Z b := by
    unfold uint.Z; rw [BitVec.toNat_umod]; push_cast; rfl
  have ea : sint.Z a = uint.Z a := by word
  have eb : sint.Z b = uint.Z b := by word
  have hlt : uint.Z (a % b) < 2 ^ 63 := by
    rw [hmod]; have := Int.emod_lt_of_pos (uint.Z a) (by omega : 0 < uint.Z b)
    have : uint.Z b < 2 ^ 63 := by word
    have := Int.emod_nonneg (uint.Z a) (by omega : uint.Z b ≠ 0)
    omega
  have e : sint.Z (a % b) = uint.Z (a % b) := by word
  rw [e, hmod, ea, eb]

theorem sint_sdiv (a b : w64) (ha : 0 ≤ sint.Z a) (hb : 0 < sint.Z b) :
    sint.Z (BitVec.sdiv a b) = sint.Z a / sint.Z b := by
  have h1 := msb_false_of_sint_nonneg a ha
  have h2 := msb_false_of_sint_nonneg b (by omega)
  have hu : BitVec.sdiv a b = a / b := by
    unfold BitVec.sdiv; rw [h1, h2]; rfl
  rw [hu]
  have hdiv : uint.Z (a / b) = uint.Z a / uint.Z b := by
    unfold uint.Z; rw [BitVec.toNat_udiv]; push_cast; rfl
  have ea : sint.Z a = uint.Z a := by word
  have eb : sint.Z b = uint.Z b := by word
  have hlt : uint.Z (a / b) < 2 ^ 63 := by
    rw [hdiv]
    have : uint.Z a < 2 ^ 63 := by word
    have := Int.ediv_le_self (uint.Z b) (by omega : 0 ≤ uint.Z a)
    have := Int.ediv_nonneg (by omega : 0 ≤ uint.Z a) (by omega : 0 ≤ uint.Z b)
    omega
  have e : sint.Z (a / b) = uint.Z (a / b) := by word
  rw [e, hdiv, ea, eb]


theorem sint_mul (a b : w64) (ha : 0 ≤ sint.Z a) (hb : 0 ≤ sint.Z b)
    (h : sint.Z a * sint.Z b < 2 ^ 63) : sint.Z (a * b) = sint.Z a * sint.Z b := by
  have ea : sint.Z a = uint.Z a := by word
  have eb : sint.Z b = uint.Z b := by word
  have hm : uint.Z (a * b) = uint.Z a * uint.Z b % 2 ^ 64 := by
    unfold uint.Z; rw [BitVec.toNat_mul, Int.natCast_emod, Int.natCast_mul, Int.natCast_pow]; rfl
  rw [ea, eb] at h ⊢
  have h0 : 0 ≤ uint.Z a * uint.Z b := Int.mul_nonneg (by word) (by word)
  have hu : uint.Z (a * b) = uint.Z a * uint.Z b := by
    rw [hm]; exact Int.emod_eq_of_lt h0 (by omega)
  have : uint.Z (a * b) < 2 ^ 63 := by omega
  have e : sint.Z (a * b) = uint.Z (a * b) := by word
  rw [e, hu]

end bbolt
end EtcdGrove
end Perennial
