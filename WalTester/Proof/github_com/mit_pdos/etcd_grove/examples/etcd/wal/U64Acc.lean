/-
Lean-first (no Rocq counterpart).

# A little-endian `uint64`, byte by byte (W4c U5)

`u64Acc x i`: the low `8 i` bits of `x`, the accumulator after `i` bytes of a little-endian decoding
(the oracle's `decoder.u64`, `DecRep.lean`; `fromRaft`'s salt, `FromRaft.lean`). `u64Acc_step`: one
byte more. Proved bit by bit (`BitVec.getLsbD`), with the masks by kernel evaluation (`decide
+kernel`): not `bv_decide`, whose proofs rest on native evaluation (`Lean.ofReduceBool`), which until
2026-11-15 put nine `_native.bv_decide` axioms in the tester's trust base.
-/
module

public import Perennial.Std.Word

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

/-- The decoded prefix after `i` bytes: the low `8 i` bits. -/
def u64Acc (x : w64) (i : Nat) : w64 := x &&& ((1 <<< (8 * i)) - 1)

theorem u64Acc_mask : ∀ i, i ≤ 8 → ((1 <<< (8 * i)) - 1 : w64) = BitVec.ofNat 64 (2 ^ (8 * i) - 1) := by
  decide +kernel

theorem getLsbD_u64Acc (x : w64) (i j : Nat) (hi : i ≤ 8) :
    (u64Acc x i).getLsbD j = (x.getLsbD j && decide (j < 8 * i)) := by
  unfold u64Acc
  rw [u64Acc_mask i hi, BitVec.getLsbD_and, BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one]
  by_cases h : j < 64
  · simp [h]
  · simp [BitVec.getLsbD_of_ge x j (by omega)]

theorem u64Acc_zero (x : w64) : u64Acc x 0 = W64 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  rw [getLsbD_u64Acc _ _ _ (by omega)]; simp [W64]

theorem u64Acc_eight (x : w64) : u64Acc x 8 = x := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  rw [getLsbD_u64Acc _ _ _ (by omega)]; simp; omega

/-- A byte, zero-extended. -/
theorem W64_uint_Z_w8 (b : w8) : W64 (uint.Z b) = b.setWidth 64 := by
  apply BitVec.eq_of_toNat_eq; simp [W64, uint.Z]

/-- The `i`-th byte of `x`. -/
theorem W8_uint_Z (v : w64) : W8 (uint.Z v) = v.setWidth 8 := by
  apply BitVec.eq_of_toNat_eq; simp [W8, uint.Z]

/-- One byte more of the decoding (`x |= uint64(b[off+i]) << (8*i)`). -/
theorem u64Acc_step (x : w64) (i : Nat) (hi : i < 8) :
    u64Acc x i ||| ((W8 (uint.Z (x >>> W64 (8 * (i : Int))))).setWidth 64 <<< (W64 8 * W64 i)) =
      u64Acc x (i + 1) := by
  have h1 : (W64 (8 * (i : Int))).toNat = 8 * i := by
    simp [W64]; omega
  have h2 : (W64 8 * W64 i).toNat = 8 * i := by
    simp [W64]; omega
  rw [W8_uint_Z, BitVec.ushiftRight_eq', BitVec.shiftLeft_eq', h1, h2]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, getLsbD_u64Acc _ _ _ (by omega : i ≤ 8),
    getLsbD_u64Acc _ _ _ (by omega : i + 1 ≤ 8)]
  by_cases a : j < 8 * i
  · simp [a, hj, show j < 8 * (i+1) by omega]
  · by_cases b : j < 8 * (i + 1)
    · have : 8 * i + (j - 8 * i) = j := by omega
      simp [a, b, hj, show j - 8 * i < 8 by omega, show j - 8 * i < 64 by omega, this]
    · have : ¬ j - 8 * i < 8 := by omega
      simp [a, b, hj, this]

/-- `u64Acc_step` with the byte zero-extended through its value (`uint64(b)`). -/
theorem u64Acc_step' (x : w64) (i : Nat) (hi : i < 8) :
    u64Acc x i ||| (W64 (uint.Z (W8 (uint.Z (x >>> W64 (8 * (i : Int)))))) <<< (W64 8 * W64 i)) =
      u64Acc x (i + 1) := by
  rw [W64_uint_Z_w8]; exact u64Acc_step x i hi

end etcd_wal
end EtcdGrove
end Perennial
