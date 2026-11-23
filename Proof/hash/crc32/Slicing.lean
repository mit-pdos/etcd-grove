/-
The CRC tables' algebra (pure; a defs module of `hash/crc32`'s proofs): `crcBits` is linear (over
`^^^`) and composes, so the byte step of `simpleUpdate` over `crcTableOf poly` is eight bitwise steps
(`crcUpdByte_tableOf`), the slicing-by-8 tables of `slicingMakeTable` are `crcBits` of `8 (j + 1)`
steps (`slicingEntry`, and their recurrence `slicingEntry_succ`), and `slicingUpdate`'s eight-byte
step computes the eight byte steps (`slicing8_step`). The bitwise identities are proved bit by bit
(`crc_bits`), so every result rests only on Lean's three axioms.
-/
module

public import Spec.hash.crc32.Model

@[expose] public section

namespace Perennial
namespace hash.crc32

/-! ## Bitwise identities

Each bitwise identity below is proved one bit at a time (`ext`, then `grind` on the bits), which the
kernel checks. `bv_decide` would add a native-evaluation axiom (`*._native.bv_decide.ax_*`, through
`Lean.ofReduceBool`) for each call. -/

/-- The bits of `0xff`: the low eight. -/
theorem getLsbD_0xff (i : Nat) : (0xff#32).getLsbD i = decide (i < 8) := by
  rw [show (0xff#32) = BitVec.ofNat 32 (2 ^ 8 - 1) from rfl, BitVec.getLsbD_ofNat,
    Nat.testBit_two_pow_sub_one]
  by_cases h : i < 8 <;> simp [h]; omega

theorem getElem_0xff (i : Nat) (h : i < 32) : (0xff#32)[i] = decide (i < 8) := by
  rw [← BitVec.getLsbD_eq_getElem, getLsbD_0xff]

/-- Prove an identity of `w32`s bit by bit: `ext`, the bits normalized by `simp` (xors in AC normal
form), and the rest (case splits on the bit index) by `grind`. -/
local macro "crc_bits" : tactic =>
  `(tactic| (ext i hi <;>
    simp [getLsbD_0xff, getElem_0xff, Bool.xor_assoc, Bool.xor_comm, Bool.xor_left_comm] <;>
    grind [getLsbD_0xff, getElem_0xff]))

/-- `crcBit` without the branch: xor `poly` exactly when the low bit is set. -/
theorem crcBit_eq (poly c : w32) :
    crcBit poly c = (c >>> 1) ^^^ (if c.getLsbD 0 then poly else 0#32) := by
  unfold crcBit
  rw [BitVec.and_one_eq_setWidth_ofBool_getLsbD]
  cases c.getLsbD 0 <;> simp

theorem crcBit_xor (poly a b : w32) : crcBit poly (a ^^^ b) = crcBit poly a ^^^ crcBit poly b := by
  rw [crcBit_eq, crcBit_eq, crcBit_eq, BitVec.getLsbD_xor]
  cases a.getLsbD 0 <;> cases b.getLsbD 0 <;> simp only [Bool.xor_self, Bool.xor_false,
    Bool.xor_true, Bool.not_false, Bool.false_eq_true, ite_false, ite_true] <;> crc_bits

theorem crcBit_zero (poly : w32) : crcBit poly 0#32 = 0#32 := by
  rw [crcBit_eq]; simp only [BitVec.getLsbD_zero, Bool.false_eq_true, ite_false]; crc_bits

theorem crcBits_xor (poly : w32) (k : Nat) (a b : w32) :
    crcBits poly k (a ^^^ b) = crcBits poly k a ^^^ crcBits poly k b := by
  induction k generalizing a b with
  | zero => rfl
  | succ k ih => simp only [crcBits, crcBit_xor, ih]

theorem crcBits_add (poly : w32) (m n : Nat) (c : w32) :
    crcBits poly (m + n) c = crcBits poly n (crcBits poly m c) := by
  induction m generalizing c with
  | zero => simp [crcBits]
  | succ m ih =>
    rw [show m + 1 + n = (m + n) + 1 by omega]
    simp only [crcBits]; exact ih _

/-- `k` steps of a word whose low `k` bits are zero only shift it. -/
theorem crcBits_lowzero (poly : w32) (k : Nat) (x : w32) (h : ∀ i < k, x.getLsbD i = false) :
    crcBits poly k x = x >>> k := by
  induction k generalizing x with
  | zero => simp [crcBits]
  | succ k ih =>
    have h0 : x.getLsbD 0 = false := h 0 (by omega)
    rw [crcBits, crcBit_eq, h0, ih]
    · crc_bits
    · intro i hi
      have := h (i + 1) (by omega)
      grind

/-- Eight steps of a word whose low byte is zero only shift it. -/
theorem crcBits8_lowzero (poly x : w32) (h : x &&& 0xff#32 = 0#32) :
    crcBits poly 8 x = x >>> 8 := by
  apply crcBits_lowzero
  intro i hi
  have := congrArg (·.getLsbD i) h
  simp only [BitVec.getLsbD_and, getLsbD_0xff, BitVec.getLsbD_zero] at this
  simpa [hi] using this

/-- Eight steps of `x`: the table entry of its low byte, xored with the rest shifted. -/
theorem crcBits8_split (poly x : w32) :
    crcBits poly 8 x = crcBits poly 8 (x &&& 0xff#32) ^^^ (x >>> 8) := by
  have hx : x = (x &&& 0xff#32) ^^^ ((x >>> 8) <<< 8) := by crc_bits
  conv => lhs; rw [hx]
  rw [crcBits_xor, crcBits8_lowzero poly ((x >>> 8) <<< 8) (by crc_bits)]
  congr 1; crc_bits

/-- `simpleUpdate`'s byte step over `poly`'s table is eight bitwise steps. -/
theorem crcUpdByte_tableOf (poly c : w32) (v : w8) :
    crcUpdByte (crcTableOf poly) c v = crcBits poly 8 (c ^^^ v.zeroExtend 32) := by
  rw [crcBits8_split poly (c ^^^ v.zeroExtend 32)]
  unfold crcUpdByte
  have hk : (BitVec.ofNat 8 c.toNat ^^^ v).toNat < 256 := BitVec.isLt _
  simp only [crcTableOf, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hk, Option.map_some, Option.getD_some, crcTableEntry]
  have h1 : BitVec.ofNat 32 (BitVec.ofNat 8 c.toNat ^^^ v).toNat = (c ^^^ v.zeroExtend 32) &&& 0xff#32 := by
    rw [BitVec.ofNat_toNat, BitVec.ofNat_toNat]; crc_bits
  have h2 : (c ^^^ v.zeroExtend 32) >>> 8 = c >>> 8 := by crc_bits
  rw [h1, h2]

/-- The bitwise CRC-32C is CRC-32C. -/
theorem crc32cBits_eq (c : w32) (p : List w8) : crc32cBits c p = crc32c c p := by
  unfold crc32cBits crc32c crcUpdate
  congr 1
  congr 1
  funext c v
  rw [crcUpdByte_tableOf]

/-! ## The slicing-by-8 tables -/

theorem slicingEntry_zero (poly : w32) (i : Nat) : slicingEntry poly 0 i = crcTableEntry poly i := rfl

/-- `slicingMakeTable`'s recurrence: `t[j+1][i] = t[0][t[j][i]&0xFF] ^ (t[j][i] >> 8)`. -/
theorem slicingEntry_succ (poly : w32) (j i : Nat) :
    slicingEntry poly (j + 1) i =
      crcTableEntry poly ((slicingEntry poly j i &&& 0xff#32).toNat) ^^^ (slicingEntry poly j i >>> 8) := by
  unfold slicingEntry crcTableEntry
  rw [show 8 * (j + 1 + 1) = 8 * (j + 1) + 8 by omega, crcBits_add, crcBits8_split, BitVec.ofNat_toNat,
    BitVec.setWidth_eq]

/-- Eight steps of a byte shifted left by eight: the byte. -/
theorem crcBits8_shl8 (poly x : w32) (h : x >>> 24 = 0#32) : crcBits poly 8 (x <<< 8) = x := by
  have hb : ∀ j, 24 ≤ j → x.getLsbD j = false := fun j hj => by
    have := congrArg (·.getLsbD (j - 24)) h
    simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_zero] at this
    rwa [Nat.add_sub_cancel' hj] at this
  rw [crcBits8_lowzero _ _ (by crc_bits)]; crc_bits
/-- The byte step in the non-complemented domain. -/
def crcStep (poly c : w32) (v : w8) : w32 := crcBits poly 8 (c ^^^ v.zeroExtend 32)

/-- Four byte steps: 32 steps of the word they are xored into, little-endian. -/
theorem crcStep4 (poly c : w32) (b0 b1 b2 b3 : w8) :
    [b0, b1, b2, b3].foldl (crcStep poly) c =
      crcBits poly 32 (c ^^^ (b0.zeroExtend 32 ||| (b1.zeroExtend 32 <<< 8) |||
        (b2.zeroExtend 32 <<< 16) ||| (b3.zeroExtend 32 <<< 24))) := by
  simp only [List.foldl, crcStep]
  -- peel one byte at a time: 32 = 8 + 24, the rest's low byte is zero
  have peel : ∀ (k : Nat) (x y : w32), y &&& 0xff#32 = 0#32 →
      crcBits poly (8 + k) (x ^^^ y) = crcBits poly k (crcBits poly 8 x ^^^ (y >>> 8)) := by
    intro k x y hy
    rw [crcBits_add, crcBits_xor, crcBits8_lowzero _ _ hy]
  rw [show crcBits poly 32 = crcBits poly (8 + (8 + (8 + 8))) from rfl]
  rw [show c ^^^ (b0.zeroExtend 32 ||| (b1.zeroExtend 32 <<< 8) ||| (b2.zeroExtend 32 <<< 16) |||
      (b3.zeroExtend 32 <<< 24)) = (c ^^^ b0.zeroExtend 32) ^^^ ((b1.zeroExtend 32 <<< 8) ^^^
      (b2.zeroExtend 32 <<< 16) ^^^ (b3.zeroExtend 32 <<< 24)) by crc_bits]
  rw [peel]
  rw [show crcBits poly 8 (c ^^^ b0.zeroExtend 32) ^^^ ((b1.zeroExtend 32 <<< 8) ^^^
      (b2.zeroExtend 32 <<< 16) ^^^ (b3.zeroExtend 32 <<< 24)) >>> 8 =
      (crcBits poly 8 (c ^^^ b0.zeroExtend 32) ^^^ b1.zeroExtend 32) ^^^
      ((b2.zeroExtend 32 <<< 8) ^^^ (b3.zeroExtend 32 <<< 16)) by crc_bits]
  rw [peel]
  rw [show (crcBits poly 8 (crcBits poly 8 (c ^^^ b0.zeroExtend 32) ^^^ b1.zeroExtend 32) ^^^
      ((b2.zeroExtend 32 <<< 8) ^^^ (b3.zeroExtend 32 <<< 16)) >>> 8) =
      (crcBits poly 8 (crcBits poly 8 (c ^^^ b0.zeroExtend 32) ^^^ b1.zeroExtend 32) ^^^
        b2.zeroExtend 32) ^^^ (b3.zeroExtend 32 <<< 8) by crc_bits]
  rw [peel]
  · congr 1; crc_bits
  all_goals crc_bits

/-- `crcBits` of a word, byte by byte: its bytes' entries of `n`, `n - 8`, `n - 16`, `n - 24` steps. -/
theorem crcBits_bytes (poly x : w32) (n : Nat) :
    crcBits poly (n + 24) x =
      crcBits poly (n + 24) (x &&& 0xff#32) ^^^ crcBits poly (n + 16) ((x >>> 8) &&& 0xff#32) ^^^
      crcBits poly (n + 8) ((x >>> 16) &&& 0xff#32) ^^^ crcBits poly n (x >>> 24) := by
  have hx : x = (x &&& 0xff#32) ^^^ ((((x >>> 8) &&& 0xff#32) <<< 8) ^^^
      ((((x >>> 16) &&& 0xff#32) <<< 16) ^^^ ((x >>> 24) <<< 24))) := by crc_bits
  conv => lhs; rw [hx]
  rw [crcBits_xor, crcBits_xor, crcBits_xor]
  have s1 : crcBits poly (n + 24) (((x >>> 8) &&& 0xff#32) <<< 8) =
      crcBits poly (n + 16) ((x >>> 8) &&& 0xff#32) := by
    rw [show n + 24 = 8 + (n + 16) by omega, crcBits_add, crcBits8_shl8]
    crc_bits
  have s2 : crcBits poly (n + 24) (((x >>> 16) &&& 0xff#32) <<< 16) =
      crcBits poly (n + 8) ((x >>> 16) &&& 0xff#32) := by
    rw [show n + 24 = 8 + (8 + (n + 8)) by omega, crcBits_add, crcBits_add,
      show ((x >>> 16) &&& 0xff#32) <<< 16 = (((x >>> 16) &&& 0xff#32) <<< 8) <<< 8 by
        simp only [← BitVec.shiftLeft_add],
      crcBits8_shl8, crcBits8_shl8]
    all_goals crc_bits
  have s3 : crcBits poly (n + 24) ((x >>> 24) <<< 24) = crcBits poly n (x >>> 24) := by
    rw [show n + 24 = 8 + (8 + (8 + n)) by omega, crcBits_add, crcBits_add, crcBits_add,
      show (x >>> 24) <<< 24 = (((x >>> 24) <<< 8) <<< 8) <<< 8 by
        simp only [← BitVec.shiftLeft_add],
      crcBits8_shl8, crcBits8_shl8, crcBits8_shl8]
    all_goals crc_bits
  rw [s1, s2, s3]
  ac_rfl

/-- **The slicing-by-8 step** (`slicingUpdate`'s loop body, `crc32_generic.go:83-87`): from `c`,
`x = c ^ LEUint32(p[0:4])`, the xor of the eight tables' entries is the eight byte steps. -/
theorem slicing8_step (poly c : w32) (b0 b1 b2 b3 b4 b5 b6 b7 : w8) :
    let x := c ^^^ (b0.zeroExtend 32 ||| (b1.zeroExtend 32 <<< 8) |||
        (b2.zeroExtend 32 <<< 16) ||| (b3.zeroExtend 32 <<< 24))
    [b0, b1, b2, b3, b4, b5, b6, b7].foldl (crcStep poly) c =
      slicingEntry poly 0 b7.toNat ^^^ slicingEntry poly 1 b6.toNat ^^^
      slicingEntry poly 2 b5.toNat ^^^ slicingEntry poly 3 b4.toNat ^^^
      slicingEntry poly 4 (x >>> 24).toNat ^^^ slicingEntry poly 5 ((x >>> 16) &&& 0xff#32).toNat ^^^
      slicingEntry poly 6 ((x >>> 8) &&& 0xff#32).toNat ^^^ slicingEntry poly 7 (x &&& 0xff#32).toNat := by
  intro x
  have h4 : [b0, b1, b2, b3].foldl (crcStep poly) c = crcBits poly 32 x := crcStep4 poly c b0 b1 b2 b3
  rw [show [b0, b1, b2, b3, b4, b5, b6, b7] = [b0, b1, b2, b3] ++ [b4, b5, b6, b7] from rfl,
    List.foldl_append, h4]
  simp only [List.foldl, crcStep, crcBits_xor]
  simp only [← crcBits_add, Nat.reduceAdd]
  have hb : ∀ (v : w8), BitVec.ofNat 32 v.toNat = v.zeroExtend 32 := fun v => by
    rw [BitVec.ofNat_toNat]
  have hw : ∀ (w : w32), BitVec.ofNat 32 w.toNat = w := fun w => by simp
  simp only [slicingEntry, hb, hw, Nat.reduceAdd, Nat.reduceMul]
  have hx := crcBits_bytes poly x 40
  simp only [Nat.reduceAdd] at hx
  rw [hx]
  ac_rfl

end hash.crc32
end Perennial
