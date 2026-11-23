/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swiftnet/codec/Bytes.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
module

public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.swift.Wire

@[expose] public section

namespace Perennial.github_com.imdea_software.swiftpaxos.examples.swiftnet

theorem u64Le_bytes (x : w64) :
    [W8 (uint.Z x), W8 (uint.Z (x >>> W64 8)), W8 (uint.Z (x >>> W64 16)),
     W8 (uint.Z (x >>> W64 24)), W8 (uint.Z (x >>> W64 32)), W8 (uint.Z (x >>> W64 40)),
     W8 (uint.Z (x >>> W64 48)), W8 (uint.Z (x >>> W64 56))] = u64Le x := by
  simp only [u64Le, u64LeDef, LittleEndian.split, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · apply BitVec.eq_of_toNat_eq
    simp [Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul]

end Perennial.github_com.imdea_software.swiftpaxos.examples.swiftnet

namespace Perennial.github_com.imdea_software.swiftpaxos.examples.swiftnet
theorem W8_uintZ (y : w64) : W8 (uint.Z y) = y.setWidth 8 := by
  apply BitVec.eq_of_toNat_eq; simp
theorem W64_uintZ8 (y : w8) : W64 (uint.Z y) = y.setWidth 64 := by
  apply BitVec.eq_of_toNat_eq; simp

theorem u64Le_or (b0 b1 b2 b3 b4 b5 b6 b7 : w8) :
    u64Le (W64 (uint.Z b0) ||| W64 (uint.Z b1) <<< W64 8 ||| W64 (uint.Z b2) <<< W64 16 |||
      W64 (uint.Z b3) <<< W64 24 ||| W64 (uint.Z b4) <<< W64 32 ||| W64 (uint.Z b5) <<< W64 40 |||
      W64 (uint.Z b6) <<< W64 48 ||| W64 (uint.Z b7) <<< W64 56) = [b0, b1, b2, b3, b4, b5, b6, b7] := by
  rw [← u64Le_bytes]
  simp only [W8_uintZ, W64_uintZ8, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · ext i hi
    obtain _|_|_|_|_|_|_|_|i := i <;> first | omega | simp [W64]

theorem leToU64_or (b0 b1 b2 b3 b4 b5 b6 b7 : w8) :
    (W64 (uint.Z b0) ||| W64 (uint.Z b1) <<< W64 8 ||| W64 (uint.Z b2) <<< W64 16 |||
      W64 (uint.Z b3) <<< W64 24 ||| W64 (uint.Z b4) <<< W64 32 ||| W64 (uint.Z b5) <<< W64 40 |||
      W64 (uint.Z b6) <<< W64 48 ||| W64 (uint.Z b7) <<< W64 56) = leToU64 [b0, b1, b2, b3, b4, b5, b6, b7] := by
  rw [← u64Le_or, u64Le_to_word]
end Perennial.github_com.imdea_software.swiftpaxos.examples.swiftnet
