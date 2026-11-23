/-
The vocabulary of `pbcodec`'s specs (#37 stage S3): the protobuf wire format of
`Proof/google_golang_org/protobuf/proto/Wire.lean` (`EtcdGrove.varintEnc`, `EtcdGrove.Wire.readVarint`,
...), which the specs of the functions state their results in, and the facts about Go's 64-bit
words the proofs use to read those definitions off the translated loops.
-/
module

public import Net.Proof.models_lab.pbcodec.Base
public import Proof.google_golang_org.protobuf.proto.Wire

@[expose] public section

set_option linter.iris.dupNamespace false

noncomputable section

namespace Perennial

namespace models_lab.pbcodec

open EtcdGrove

/-- Go's `x >> 7` on a `uint64`. -/
theorem shr7 (x : w64) : uint.nat (x >>> W64 7) = uint.nat x / 128 := by
  show (x >>> W64 7).toNat = x.toNat / 128
  have : (W64 7).toNat = 7 := rfl
  rw [BitVec.ushiftRight_eq', BitVec.toNat_ushiftRight, this, Nat.shiftRight_eq_div_pow]

theorem or128_fin : ∀ a : Fin 128, ((BitVec.ofNat 8 a.val ||| BitVec.ofNat 8 128 : w8)) =
    BitVec.ofNat 8 (a.val + 128) := by decide

/-- Go's `byte(x&0x7f)|0x80`: the low seven bits of `x` with the continuation bit. -/
theorem lowByte (x : w64) : (W8 (uint.Z (x &&& W64 127)) ||| W8 128 : w8) = W8 (uint.nat x % 128 + 128) := by
  have h1 : uint.Z (x &&& W64 127) = ((uint.nat x % 128 : Nat) : Int) := by
    simp only [uint.Z, uint.nat]
    have : (W64 127) = BitVec.ofNat 64 (2 ^ 7 - 1) := rfl
    rw [this, BitVec.toNat_and]
    have h := Nat.and_two_pow_sub_one_eq_mod x.toNat 7
    simp only [BitVec.toNat_ofNat] at h ⊢
    rw [show (2 ^ 7 - 1) % 2 ^ 64 = 2 ^ 7 - 1 by decide, h]
  rw [h1]
  have := or128_fin ⟨uint.nat x % 128, Nat.mod_lt _ (by decide)⟩
  simp only at this
  have e1 : (W8 ((uint.nat x % 128 : Nat) : Int) : w8) = BitVec.ofNat 8 (uint.nat x % 128) := by
    simp only [W8]; exact BitVec.ofInt_natCast _ _
  have e2 : (W8 128 : w8) = BitVec.ofNat 8 128 := rfl
  have e3 : (W8 ((uint.nat x % 128 + 128 : Nat) : Int) : w8) = BitVec.ofNat 8 (uint.nat x % 128 + 128) := by
    simp only [W8]; exact BitVec.ofInt_natCast _ _
  rw [e1, e2, this]
  exact e3.symm

/-- An `int` holding a value below `2^63` (a size the code adds up without overflow). -/
theorem sintW64 (z : Int) (h0 : 0 ≤ z) (h1 : z < 2 ^ 63) : sint.Z (W64 z) = z := by
  simp only [sint.Z, W64, BitVec.toInt_ofInt]
  rw [Int.bmod_eq_of_le] <;> omega

/-- A word as the `W64` of its value (to add sizes up as `W64`s of naturals: `BitVec.ofInt_add`). -/
theorem w64OfNat (x : w64) (L : Nat) (h : uint.nat x = L) : x = W64 (L : Int) := by
  subst h; simp [W64, uint.nat]

/-- A non-negative `int`'s value is its unsigned one (a slice's length). -/
theorem uintOfSint (s : w64) (L : Nat) (h : L = sint.nat s ∧ 0 ≤ sint.Z s) : uint.nat s = L := by
  obtain ⟨h1, h2⟩ := h; subst h1; word

/-- Go's `uint64(k)` of a `uint32` (zero extension) keeps its value. -/
theorem zext32 (k : w32) : uint.nat (W64 (uint.Z k)) = uint.nat k := by word

/-- Go's `num<<3|typ&7` (`AppendTag`'s varint) is `num * 8 + typ` for a number below `2^61` and a
wire type below 8. -/
theorem shl3_and7 (x y : w64) : (x <<< (3 : Nat)) &&& (y &&& 7#64) = 0#64 := by
  ext i hi
  simp only [BitVec.getElem_and, BitVec.getElem_shiftLeft, BitVec.getElem_zero]
  by_cases h : i < 3
  · simp [h]
  · have : (7#64)[i] = false := by
      simp only [BitVec.getElem_eq_testBit_toNat, BitVec.toNat_ofNat]
      have : 7 >>> i = 0 := by
        rw [Nat.shiftRight_eq_div_pow]; apply Nat.div_eq_of_lt
        exact Nat.lt_of_lt_of_le (by decide : 7 < 2 ^ 3) (Nat.pow_le_pow_right (by decide) (by omega))
      simp [Nat.testBit, this]
    simp [h, this]

theorem tagWord (num typ : w64) (h1 : uint.nat num < 2 ^ 61) (h2 : uint.nat typ < 8) :
    uint.nat ((num <<< W64 3) ||| (typ &&& W64 7)) = uint.nat num * 8 + uint.nat typ := by
  have e3 : num <<< W64 3 = num <<< (3 : Nat) := by
    rw [BitVec.shiftLeft_eq']; rfl
  have e7 : (W64 7 : w64) = 7#64 := rfl
  rw [e3, e7, ← BitVec.add_eq_or_of_and_eq_zero _ _ (shl3_and7 num typ)]
  simp only [uint.nat] at h1 h2 ⊢
  rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_and, Nat.shiftLeft_eq]
  have h7 : typ.toNat &&& (7#64).toNat = typ.toNat := by
    have := Nat.and_two_pow_sub_one_eq_mod typ.toNat 3
    simp only [BitVec.toNat_ofNat]
    rw [show 7 % 2 ^ 64 = 2 ^ 3 - 1 by decide, this]
    omega
  rw [h7]
  omega

/-- A varint of a value of at least 128: its low seven bits with the continuation bit, then the
varint of the rest (`varintEnc`'s second case, for a word). -/
theorem varintEnc_w64_ge (x : w64) (h : ¬ uint.nat x < 128) :
    varintEnc (uint.nat x) =
      W8 (uint.nat x % 128 + 128) :: varintEnc (uint.nat (x >>> W64 7)) := by
  rw [varintEnc, dite_eq_right_iff.mpr (fun h' => absurd h' h), shr7]

/-- A varint of a value below 128: its one byte. -/
theorem varintEnc_w64_lt (x : w64) (h : uint.nat x < 128) : varintEnc (uint.nat x) = [W8 (uint.nat x)] := by
  rw [varintEnc, dite_eq_left h]

theorem varintSize_w64_ge (x : w64) (h : ¬ uint.nat x < 128) :
    varintSize (uint.nat x) = varintSize (uint.nat (x >>> W64 7)) + 1 := by
  unfold varintSize; rw [varintEnc_w64_ge x h]; simp

theorem varintSize_w64_lt (x : w64) (h : uint.nat x < 128) : varintSize (uint.nat x) = 1 := by
  unfold varintSize; rw [varintEnc_w64_lt x h]; rfl

/-- A varint of a value below `2^(7(k+1))` has at most `k + 1` bytes. -/
theorem varintSize_le_of (k : Nat) : ∀ n, n < 2 ^ (7 * (k + 1)) → varintSize n ≤ k + 1 := by
  induction k with
  | zero =>
    intro n hn
    unfold varintSize; rw [varintEnc, dite_eq_left (by simpa using hn)]; simp
  | succ k ih =>
    intro n hn
    unfold varintSize
    rw [varintEnc]
    split
    · simp
    · simp only [List.length_cons]
      have h2 : n / 128 < 2 ^ (7 * (k + 1)) := by
        rw [Nat.div_lt_iff_lt_mul (by decide)]
        rw [show 7 * (k + 1 + 1) = 7 * (k + 1) + 7 by omega, Nat.pow_add] at hn
        simpa using hn
      have := ih (n / 128) h2
      unfold varintSize at this
      omega

/-- A varint of a 64-bit value has at most ten bytes. -/
theorem varintSize_le (n : Nat) (h : n < 2 ^ 64) : varintSize n ≤ 10 :=
  varintSize_le_of 9 n (Nat.lt_of_lt_of_le h (by decide))

end models_lab.pbcodec
end Perennial
