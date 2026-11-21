/-
Lemmas of `encoding/base64`'s proofs: an `Encoding`'s points-to as its fields' (the proof mode's
`Access` search does not find the fields of this struct by itself), and arithmetic. Lean-first.
-/
module

public import Proof.encoding.base64.Defs
public import Perennial.Golang.Theory.Plain

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace base64

open Iris Iris.BI Iris.ProofMode

section arith

theorem sdiv_nn (a b : w64) (ha : a.msb = false) (hb : b.msb = false) : BitVec.sdiv a b = a / b := by
  rw [BitVec.sdiv_eq, ha, hb]; rfl

theorem srem_nn (a b : w64) (ha : a.msb = false) (hb : b.msb = false) : BitVec.srem a b = a % b := by
  rw [BitVec.srem_eq, ha, hb]

theorem msb_small (a : w64) (h : a.toNat < 2 ^ 63) : a.msb = false := by
  rw [BitVec.msb_eq_decide]; simp only [decide_eq_false_iff_not, Nat.not_le]; omega

/-- `EncodedLen`'s value without padding. -/
theorem encLen_nopad_eq (n : w64) (hn0 : 0 ≤ sint.Z n) (hn1 : sint.Z n < 2 ^ 62) :
    BitVec.sdiv n (W64 3) * W64 4 + BitVec.sdiv (BitVec.srem n (W64 3) * W64 8 + W64 5) (W64 6) =
        W64 (encLen none (sint.nat n) : Int) := by
  simp only [encLen, Option.isSome_none, Bool.false_eq_true, ite_false]
  have hn : n.toNat < 2 ^ 62 := by word
  have h4 : sint.nat n = n.toNat := by word
  simp only [show (W64 3 : w64) = 3#64 from rfl, show (W64 4 : w64) = 4#64 from rfl,
    show (W64 5 : w64) = 5#64 from rfl, show (W64 6 : w64) = 6#64 from rfl,
    show (W64 8 : w64) = 8#64 from rfl, h4]
  have q1 : (n / 3#64).toNat = n.toNat / 3 := by simp [BitVec.toNat_udiv]
  have q2 : (n % 3#64).toNat = n.toNat % 3 := by simp [BitVec.toNat_umod]
  have q3 : (n / 3#64 * 4#64).toNat = n.toNat / 3 * 4 := by
    rw [BitVec.toNat_mul, q1]; simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; omega
  have q4 : (n % 3#64 * 8#64 + 5#64).toNat = n.toNat % 3 * 8 + 5 := by
    rw [BitVec.toNat_add, BitVec.toNat_mul, q2]; simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; omega
  have q5 : ((n % 3#64 * 8#64 + 5#64) / 6#64).toNat = (n.toNat % 3 * 8 + 5) / 6 := by
    rw [BitVec.toNat_udiv, q4]; simp
  rw [sdiv_nn _ _ (msb_small _ (by omega)) (by decide), srem_nn _ _ (msb_small _ (by omega)) (by decide)]
  rw [sdiv_nn _ _ (msb_small _ (by omega)) (by decide)]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, q3, q5]
  simp only [BitVec.toNat_ofInt, Nat.reducePow]
  omega

/-- `EncodedLen`'s value with padding. -/
theorem encLen_pad_eq (p : w8) (n : w64) (hn0 : 0 ≤ sint.Z n) (hn1 : sint.Z n < 2 ^ 62) :
    BitVec.sdiv (n + W64 2) (W64 3) * W64 4 = W64 (encLen (some p) (sint.nat n) : Int) := by
  simp only [encLen, Option.isSome_some, ite_true]
  have hn : n.toNat < 2 ^ 62 := by word
  have h4 : sint.nat n = n.toNat := by word
  simp only [show (W64 2 : w64) = 2#64 from rfl, show (W64 3 : w64) = 3#64 from rfl,
    show (W64 4 : w64) = 4#64 from rfl, h4]
  have q0 : (n + 2#64).toNat = n.toNat + 2 := by
    rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; omega
  have q1 : ((n + 2#64) / 3#64).toNat = (n.toNat + 2) / 3 := by rw [BitVec.toNat_udiv, q0]; simp
  rw [sdiv_nn _ _ (msb_small _ (by omega)) (by decide)]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_mul, q1]
  simp only [BitVec.toNat_ofInt, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  omega

theorem w64_of_w8 (b : w8) : W64 (uint.Z b) = BitVec.setWidth 64 b := by
  apply BitVec.eq_of_toNat_eq
  simp

theorem sint_setWidth (x : w8) : sint.Z (BitVec.setWidth 64 x) = (x.toNat : Int) := by
  rw [← w64_of_w8]
  have : (x.toNat : Int) = uint.Z x := rfl
  rw [this]
  word

/-! The pieces' arithmetic, by their values (`toNat`), not `bv_decide`, whose proof rests on native
evaluation (`Lean.ofReduceBool`): a disjoint `|||` is a sum (`or_add`), a mask `&&& (2^k - 1)` a
remainder. -/

private theorem or_add (a b k : Nat) (hb : b < 2 ^ k) : a * 2 ^ k ||| b = a * 2 ^ k + b := by
  rw [Nat.mul_comm]; exact (Nat.two_pow_add_eq_or_of_lt hb a).symm

private theorem w8_lt (b : w8) : b.toNat < 256 := b.isLt

/-- The value of a byte's 64-bit widening shifted left by `k`. -/
private theorem sw_shl (b : w8) (k : Nat) (hk : k ≤ 56) :
    (BitVec.setWidth 64 b <<< (BitVec.ofNat 64 k)).toNat = b.toNat * 2 ^ k := by
  have hb := w8_lt b
  have hk' : (BitVec.ofNat 64 k).toNat = k := by
    simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by
      have : k < 2 ^ 64 := Nat.lt_of_le_of_lt hk (by decide)
      exact this)
  rw [BitVec.shiftLeft_eq', hk', BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (by omega : b.toNat < 2 ^ 64)]
  apply Nat.mod_eq_of_lt
  have : 2 ^ k ≤ 2 ^ 56 := Nat.pow_le_pow_right (by decide) hk
  have : b.toNat * 2 ^ k < 256 * 2 ^ 56 := Nat.lt_of_lt_of_le
    (Nat.mul_lt_mul_of_pos_right hb (Nat.two_pow_pos k)) (Nat.mul_le_mul_left _ this)
  exact Nat.lt_of_lt_of_le this (by decide)

private theorem sw_val (b : w8) : (BitVec.setWidth 64 b).toNat = b.toNat := by
  rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (w8_lt b) (by decide))

/-- A 64-bit value's `v >>> s &&& 63`, by its value. -/
private theorem piece64 (v : w64) (s : Nat) (hs : s < 64) :
    (v >>> (BitVec.ofNat 64 s) &&& 63#64).toNat = v.toNat / 2 ^ s % 64 := by
  have hs' : (BitVec.ofNat 64 s).toNat = s := by
    simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (Nat.lt_trans hs (by decide))
  rw [BitVec.toNat_and, BitVec.ushiftRight_eq', hs', BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have : (63#64).toNat = 2 ^ 6 - 1 := rfl
  rw [this, Nat.and_two_pow_sub_one_eq_mod]

private theorem mask64 (v : w64) : (v &&& 63#64).toNat = v.toNat % 64 := by
  rw [BitVec.toNat_and]
  have : (63#64).toNat = 2 ^ 6 - 1 := rfl
  rw [this, Nat.and_two_pow_sub_one_eq_mod]

/-- The byte pieces, by their values. -/
private theorem shr8 (b : w8) (k : Nat) : (b >>> k).toNat = b.toNat / 2 ^ k := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

private theorem and8 (b : w8) (k : Nat) (hk : k ≤ 8) :
    (b &&& BitVec.ofNat 8 (2 ^ k - 1)).toNat = b.toNat % 2 ^ k := by
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt, Nat.and_two_pow_sub_one_eq_mod]
  have : 2 ^ k ≤ 2 ^ 8 := Nat.pow_le_pow_right (by decide) hk
  have := Nat.two_pow_pos k
  omega

private theorem shl8 (x : w8) (k : Nat) : (x <<< k).toNat = x.toNat * 2 ^ k % 256 := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]

private theorem hi8 (b0 : w8) : (b0 >>> 2).toNat = b0.toNat / 4 := shr8 b0 2

private theorem mid8 (b0 b1 : w8) :
    ((b0 &&& 3) <<< 4 ||| b1 >>> 4).toNat = b0.toNat % 4 * 16 + b1.toNat / 16 := by
  have h0 := w8_lt b0; have h1 := w8_lt b1
  rw [BitVec.toNat_or, shl8, shr8, show (3 : w8) = BitVec.ofNat 8 (2 ^ 2 - 1) from rfl, and8 _ 2 (by decide)]
  have e : b0.toNat % 2 ^ 2 * 2 ^ 4 % 256 = b0.toNat % 4 * 2 ^ 4 := by
    simp only [Nat.reducePow]; omega
  rw [e, or_add _ _ 4 (by simp only [Nat.reducePow]; omega)]

private theorem mid8' (b0 : w8) : ((b0 &&& 3) <<< 4).toNat = b0.toNat % 4 * 16 := by
  have h0 := w8_lt b0
  rw [shl8, show (3 : w8) = BitVec.ofNat 8 (2 ^ 2 - 1) from rfl, and8 _ 2 (by decide)]
  simp only [Nat.reducePow]; omega

private theorem low8 (b1 b2 : w8) :
    ((b1 &&& 15) <<< 2 ||| b2 >>> 6).toNat = b1.toNat % 16 * 4 + b2.toNat / 64 := by
  have h1 := w8_lt b1; have h2 := w8_lt b2
  rw [BitVec.toNat_or, shl8, shr8, show (15 : w8) = BitVec.ofNat 8 (2 ^ 4 - 1) from rfl,
    and8 _ 4 (by decide)]
  have e : b1.toNat % 2 ^ 4 * 2 ^ 2 % 256 = b1.toNat % 16 * 2 ^ 2 := by
    simp only [Nat.reducePow]; omega
  rw [e, or_add _ _ 2 (by simp only [Nat.reducePow]; omega)]

private theorem low8' (b1 : w8) : ((b1 &&& 15) <<< 2).toNat = b1.toNat % 16 * 4 := by
  have h1 := w8_lt b1
  rw [shl8, show (15 : w8) = BitVec.ofNat 8 (2 ^ 4 - 1) from rfl, and8 _ 4 (by decide)]
  simp only [Nat.reducePow]; omega

private theorem last8 (b2 : w8) : (b2 &&& 63).toNat = b2.toNat % 64 := by
  rw [show (63 : w8) = BitVec.ofNat 8 (2 ^ 6 - 1) from rfl, and8 _ 6 (by decide)]

/-- The four 6-bit pieces of a 3-byte group, as `Encode` computes them. -/
theorem idx3 (b0 b1 b2 : w8) :
    let v := W64 (uint.Z b0) <<< W64 16 ||| W64 (uint.Z b1) <<< W64 8 ||| W64 (uint.Z b2)
    v >>> W64 18 &&& W64 63 = BitVec.setWidth 64 (b0 >>> 2) ∧
    v >>> W64 12 &&& W64 63 = BitVec.setWidth 64 (((b0 &&& 3) <<< 4) ||| (b1 >>> 4)) ∧
    v >>> W64 6 &&& W64 63 = BitVec.setWidth 64 (((b1 &&& 15) <<< 2) ||| (b2 >>> 6)) ∧
    v &&& W64 63 = BitVec.setWidth 64 (b2 &&& 63) := by
  intro v
  have h0 := w8_lt b0; have h1 := w8_lt b1; have h2 := w8_lt b2
  have hv : v.toNat = b0.toNat * 65536 + (b1.toNat * 256 + b2.toNat) := by
    simp only [v, w64_of_w8, BitVec.or_assoc, BitVec.toNat_or]
    rw [show (W64 16 : w64) = BitVec.ofNat 64 16 from rfl, show (W64 8 : w64) = BitVec.ofNat 64 8 from rfl,
      sw_shl _ 16 (by decide), sw_shl _ 8 (by decide), sw_val, or_add _ _ 8 (by simp only [Nat.reducePow]; omega),
      or_add _ _ 16 (by simp only [Nat.reducePow]; omega)]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply BitVec.eq_of_toNat_eq
  · rw [show (W64 18 : w64) = BitVec.ofNat 64 18 from rfl, show (W64 63 : w64) = 63#64 from rfl,
      piece64 _ 18 (by decide), hv, sw_val, hi8]; simp only [Nat.reducePow]; omega
  · rw [show (W64 12 : w64) = BitVec.ofNat 64 12 from rfl, show (W64 63 : w64) = 63#64 from rfl,
      piece64 _ 12 (by decide), hv, sw_val, mid8]; simp only [Nat.reducePow]; omega
  · rw [show (W64 6 : w64) = BitVec.ofNat 64 6 from rfl, show (W64 63 : w64) = 63#64 from rfl,
      piece64 _ 6 (by decide), hv, sw_val, low8]; simp only [Nat.reducePow]; omega
  · rw [show (W64 63 : w64) = 63#64 from rfl, mask64, hv, sw_val, last8]; omega

/-- The pieces of a final group of one byte. -/
theorem idx1 (b0 : w8) :
    let v := W64 (uint.Z b0) <<< W64 16
    v >>> W64 18 &&& W64 63 = BitVec.setWidth 64 (b0 >>> 2) ∧
    v >>> W64 12 &&& W64 63 = BitVec.setWidth 64 ((b0 &&& 3) <<< 4) := by
  intro v
  have h0 := w8_lt b0
  have hv : v.toNat = b0.toNat * 65536 := by
    simp only [v, w64_of_w8]
    rw [show (W64 16 : w64) = BitVec.ofNat 64 16 from rfl, sw_shl _ 16 (by decide)]
  refine ⟨?_, ?_⟩ <;> apply BitVec.eq_of_toNat_eq
  · rw [show (W64 18 : w64) = BitVec.ofNat 64 18 from rfl, show (W64 63 : w64) = 63#64 from rfl,
      piece64 _ 18 (by decide), hv, sw_val, hi8]; simp only [Nat.reducePow]; omega
  · rw [show (W64 12 : w64) = BitVec.ofNat 64 12 from rfl, show (W64 63 : w64) = 63#64 from rfl,
      piece64 _ 12 (by decide), hv, sw_val, mid8']; simp only [Nat.reducePow]; omega

/-- The pieces of a final group of two bytes. -/
theorem idx2 (b0 b1 : w8) :
    let v := W64 (uint.Z b0) <<< W64 16 ||| W64 (uint.Z b1) <<< W64 8
    v >>> W64 18 &&& W64 63 = BitVec.setWidth 64 (b0 >>> 2) ∧
    v >>> W64 12 &&& W64 63 = BitVec.setWidth 64 (((b0 &&& 3) <<< 4) ||| (b1 >>> 4)) ∧
    v >>> W64 6 &&& W64 63 = BitVec.setWidth 64 ((b1 &&& 15) <<< 2) := by
  intro v
  have h0 := w8_lt b0; have h1 := w8_lt b1
  have hv : v.toNat = b0.toNat * 65536 + b1.toNat * 256 := by
    simp only [v, w64_of_w8, BitVec.toNat_or]
    rw [show (W64 16 : w64) = BitVec.ofNat 64 16 from rfl, show (W64 8 : w64) = BitVec.ofNat 64 8 from rfl,
      sw_shl _ 16 (by decide), sw_shl _ 8 (by decide), or_add _ _ 16 (by simp only [Nat.reducePow]; omega)]
  refine ⟨?_, ?_, ?_⟩ <;> apply BitVec.eq_of_toNat_eq
  · rw [show (W64 18 : w64) = BitVec.ofNat 64 18 from rfl, show (W64 63 : w64) = 63#64 from rfl,
      piece64 _ 18 (by decide), hv, sw_val, hi8]; simp only [Nat.reducePow]; omega
  · rw [show (W64 12 : w64) = BitVec.ofNat 64 12 from rfl, show (W64 63 : w64) = 63#64 from rfl,
      piece64 _ 12 (by decide), hv, sw_val, mid8]; simp only [Nat.reducePow]; omega
  · rw [show (W64 6 : w64) = BitVec.ofNat 64 6 from rfl, show (W64 63 : w64) = 63#64 from rfl,
      piece64 _ 6 (by decide), hv, sw_val, low8']; simp only [Nat.reducePow]; omega

theorem lt64 (x : w8) (h : x < 64#8) : x.toNat < 64 := by
  rw [BitVec.lt_def] at h; simpa using h

/-! The 6-bit pieces are below 64. -/
theorem pc0 (b0 : w8) : b0 >>> 2 < 64#8 := by
  rw [BitVec.lt_def, hi8]; have := w8_lt b0; simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; omega
theorem pc1 (b0 b1 : w8) : ((b0 &&& 3) <<< 4 ||| b1 >>> 4) < 64#8 := by
  rw [BitVec.lt_def, mid8]; have := w8_lt b1; simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; omega
theorem pc1' (b0 : w8) : (b0 &&& 3) <<< 4 < 64#8 := by
  rw [BitVec.lt_def, mid8']; simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; omega
theorem pc2 (b1 b2 : w8) : ((b1 &&& 15) <<< 2 ||| b2 >>> 6) < 64#8 := by
  rw [BitVec.lt_def, low8]; have := w8_lt b2; simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; omega
theorem pc2' (b1 : w8) : (b1 &&& 15) <<< 2 < 64#8 := by
  rw [BitVec.lt_def, low8']; simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; omega
theorem pc3 (b2 : w8) : b2 &&& 63 < 64#8 := by
  rw [BitVec.lt_def, last8]; simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; omega

/-- A 6-bit piece is a valid index of the alphabet. -/
theorem idx_bound (x : w8) (h : x.toNat < 64) :
    0 ≤ sint.Z (BitVec.setWidth 64 x) ∧ sint.Z (BitVec.setWidth 64 x) < 64 := by
  rw [sint_setWidth]; omega

end arith

section slices
variable [GooseExts] [GoLocalContext] [GoGlobalContext] [GoSemanticsFunctions] [go.PreSemantics]

/-- An element of a sub-slice is an element of the slice. -/
theorem sliceIndexRef_slice (V : Type) (s : GoSlice) (low high : w64) (i : Int) :
    sliceIndexRef V i (slice.slice s V low high) = sliceIndexRef V (sint.Z low + i) s := by
  simp only [slice.slice, sliceIndexRef]
  rw [← go.arrayIndexRef_add]

end slices

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.encoding.base64.Assumptions]

/-- The fields of an `Encoding` at `e`. -/
abbrev encFields (e : Loc) (enc : _root_.Perennial.encoding.base64.Encoding) (dq : DFrac) :
    IProp GF :=
  iprop(structFieldRef _root_.Perennial.encoding.base64.Encoding go!"encode" e ↦{dq} enc.encode' ∗
    structFieldRef _root_.Perennial.encoding.base64.Encoding go!"decodeMap" e ↦{dq} enc.decodeMap' ∗
    structFieldRef _root_.Perennial.encoding.base64.Encoding go!"padChar" e ↦{dq} enc.padChar' ∗
    structFieldRef _root_.Perennial.encoding.base64.Encoding go!"strict" e ↦{dq} enc.strict')

theorem enc_open (e : Loc) (enc : _root_.Perennial.encoding.base64.Encoding) (dq : DFrac) :
    (e ↦{dq} enc : IProp GF) ⊢ ⌜e ≠ null⌝ ∗ encFields e enc dq := by
  iintro He
  icases typedPointsto_not_null_dup _ _ _ $$ He with ⟨He, %Hnn⟩
  icases typedPointsto_split _ _ _ $$ He with He
  simp only [TypedPointsto.typedPointstoDef]
  icases He with ⟨H1, H2, H3, H4, -⟩
  isplitr
  · ipureintro; exact Hnn
  isplitl [H1]
  · iexact H1
  isplitl [H2]
  · iexact H2
  isplitl [H3]
  · iexact H3
  iexact H4

theorem enc_close (e : Loc) (enc : _root_.Perennial.encoding.base64.Encoding) (dq : DFrac)
    (h : e ≠ null) :
    encFields (GF := GF) e enc dq ⊢ e ↦{dq} enc := by
  iintro ⟨H1, H2, H3, H4⟩
  iapply typedPointsto_combine _ _ _ h
  simp only [TypedPointsto.typedPointstoDef]
  isplitl [H1]
  · iexact H1
  isplitl [H2]
  · iexact H2
  isplitl [H3]
  · iexact H3
  isplitl [H4]
  · iexact H4
  itrivial

/-- A byte slice's bytes are in memory, below `maxAddr` (`2^47`): there are at most that many. -/
theorem bytes_len_le (s : GoSlice) (dq : DFrac) (d : List w8) :
    (s ↦*{dq} d : IProp GF) ⊢ ⌜d.length ≤ 2 ^ 47⌝ := by
  rw [ownSlice_unseal]; unfold ownSliceDef
  iintro (%H | ⟨H, %_⟩)
  · obtain ⟨_, rfl⟩ := H
    ipureintro; simp
  · rcases d with _ | ⟨b, bs⟩
    · ipureintro; simp
    icases array_len _ _ _ _ $$ H with %Hlen
    icases typedPointsto_byte_array_bounds _ _ (array.mk (sint.Z s.len) (b :: bs)) dq (by simp) $$ H
      with %Hb
    ipureintro
    have : maxAddr = 2 ^ 47 := rfl
    omega

/-- A load of the `i`-th byte of a byte array. -/
theorem wp_load_arr (l : Loc) (n : Int) (a : GoArray w8 n) (dq : DFrac) (i : Int) (hi : 0 ≤ i ∧ i < n) :
    {{ (l ↦{dq} a : IProp GF) }}
      (App (Val (GoInstruction (GoLoad go.byte))) (Val #(arrayIndexRef w8 i l)))
    {{ RET #(a.arr.getD i.toNat 0); l ↦{dq} a }} := by
  iintro %Φ Ha HΦ
  obtain ⟨arr⟩ := a
  icases array_len _ _ _ _ $$ Ha with %Hlen
  have hlk : arr[i.toNat]? = some (arr.getD i.toNat 0) := by
    rw [List.getElem?_eq_getElem (by omega)]; simp [List.getD, List.getElem?_eq_getElem (show i.toNat < arr.length by omega)]
  icases array_acc _ i dq n ⟨arr⟩ (arr.getD i.toNat 0) hi.1 hlk $$ Ha with ⟨Hv, Ha⟩
  wp_apply IntoValTyped.wp_load (t := go.byte) _ _ _ $$ Hv as Hv
  iapply HΦ
  ihave Ha := Ha $$ Hv
  rw [list_set_lookup_self arr i.toNat _ hlk]
  iexact Ha

/-- A store of the `i`-th byte of a byte array. -/
theorem wp_store_arr (l : Loc) (n : Int) (a : GoArray w8 n) (i : Int) (v : w8) (hi : 0 ≤ i ∧ i < n) :
    {{ (l ↦ a : IProp GF) }}
      (App (Val (GoInstruction (GoStore go.byte))) (Val (PairV #(arrayIndexRef w8 i l) #v)))
    {{ RET #(); l ↦ (array.mk n (a.arr.set i.toNat v) : GoArray w8 n) }} := by
  iintro %Φ Ha HΦ
  obtain ⟨arr⟩ := a
  icases array_len _ _ _ _ $$ Ha with %Hlen
  have hlk : arr[i.toNat]? = some (arr.getD i.toNat 0) := by
    rw [List.getElem?_eq_getElem (by omega)]; simp [List.getD, List.getElem?_eq_getElem (show i.toNat < arr.length by omega)]
  icases array_acc _ i (DFrac.own 1) n ⟨arr⟩ (arr.getD i.toNat 0) hi.1 hlk $$ Ha with ⟨Hv, Ha⟩
  wp_apply IntoValTyped.wp_store (t := go.byte) _ _ _ $$ Hv as Hv
  iapply HΦ
  iapply Ha $$ Hv

/-- A load of the `i`-th symbol of an `Encoding`'s alphabet. -/
theorem wp_load_alpha (e : Loc) (a : GoArray w8 64) (dqe : DFrac) (i : Int) (hi : 0 ≤ i ∧ i < 64) :
    {{ (structFieldRef _root_.Perennial.encoding.base64.Encoding go!"encode" e ↦{dqe} a : IProp GF) }}
      (App (Val (GoInstruction (GoLoad go.byte)))
        (Val #(arrayIndexRef w8 i (structFieldRef _root_.Perennial.encoding.base64.Encoding go!"encode" e))))
    {{ RET #(a.arr.getD i.toNat 0);
        structFieldRef _root_.Perennial.encoding.base64.Encoding go!"encode" e ↦{dqe} a }} :=
  wp_load_arr _ 64 a dqe i hi

/-- A whole byte array as the slice `a[0:n]`. -/
theorem array_slice0 (l : Loc) (n : Int) (a : GoArray w8 n) (hn : n < 2 ^ 63) :
    (l ↦ a : IProp GF) ⊢ slice.mk (arrayIndexRef w8 (sint.Z (W64 0)) l) (W64 n - W64 0) (W64 n - W64 0) ↦* a.arr := by
  iintro Ha
  icases array_len _ _ _ _ $$ Ha with %Hlen
  have h0 : sint.Z (W64 0) = 0 := rfl
  rw [h0, go.arrayIndexRef_0, show W64 n - W64 0 = W64 n by simp]
  iapply slice_array l n a (by omega) $$ Ha

/-- Back: the slice `a[0:n]` as the array. -/
theorem slice0_array (l : Loc) (n : Int) (vs : List w8) (hn : 0 < n ∧ n < 2 ^ 63) :
    (slice.mk (arrayIndexRef w8 (sint.Z (W64 0)) l) (W64 n - W64 0) (W64 n - W64 0) ↦* vs : IProp GF) ⊢
      l ↦ (array.mk n vs : GoArray w8 n) := by
  have h0 : sint.Z (W64 0) = 0 := rfl
  rw [h0, go.arrayIndexRef_0, show W64 n - W64 0 = W64 n by simp]
  rw [ownSlice_unseal]; unfold ownSliceDef
  iintro (%H | ⟨H, %_⟩)
  · exfalso
    obtain ⟨H, _⟩ := H
    have := congrArg GoSlice.len H
    simp only [slice.nil] at this
    revert this; word
  · have : sint.Z (W64 n) = n := by word
    simp only
    rw [this]
    iexact H

end lemmas

end base64
end EtcdGrove
end Perennial
