/-
**The WAL's framing** (pure; W1 of `notes/wal-fsext-plan.md`, §2.3 "Framing"). The Go reference is
the WAL at the pin (`go.etcd.io/etcd/server/v3/storage/wal`, fork commit `0b50f04262d9`):
`encoder.go` (`encodeFrameSize`, :100-108; `prepareDataWithPadding`, :116-122; `write`, :124-),
`decoder.go` (`decodeFrameSize`, :157-166; `isTornEntry`, :170-203).

A record's bytes `d` are written as a *frame*: the 8-byte little-endian length word, `d`, then 0-7
zero bytes of padding up to a multiple of 8. The length word holds `|d|` in its low 56 bits and,
when there is padding, `0x80 | pad` in its top byte (so it reads as a negative `int64`).
-/
module

public import Perennial.Std.Word.LittleEndian

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace WalEnc

/-- The padding `encodeFrameSize` adds to `n` data bytes (encoder.go:103). -/
def framePad (n : Nat) : Nat := (8 - n % 8) % 8

/-- **`encodeFrameSize(dataBytes)`** (encoder.go:100-108): the length word and the padding. -/
def encodeFrameSize (n : Nat) : w64 × Nat :=
  let lenField : w64 := BitVec.ofNat 64 n
  let pad := framePad n
  (if pad ≠ 0 then lenField ||| ((0x80#64 ||| BitVec.ofNat 64 pad) <<< 56) else lenField, pad)

/-- **`decodeFrameSize(lenField)`** (decoder.go:157-166): the record's byte count (the low 56
bits) and the padding (the low 3 bits of the top byte, when the word is negative). -/
def decodeFrameSize (l : w64) : Nat × Nat :=
  (uint.nat (l &&& ~~~(0xff#64 <<< 56)),
   if l.slt 0#64 then uint.nat ((l >>> 56) &&& 7#64) else 0)

/-- **The frame of a record's bytes `d`** (`prepareDataWithPadding` then `write`: the length word
by `binary.LittleEndian.PutUint64`, then the padded data). -/
def frame (d : List w8) : List w8 :=
  u64Le (encodeFrameSize d.length).1 ++ d ++ List.replicate (framePad d.length) (0#8)

/-- The frames of several records, concatenated (what the page writer writes, in order). -/
def frames (ds : List (List w8)) : List w8 := ds.flatMap frame

/-! ## Sector chunks (`isTornEntry`) -/

/-- The sector size the decoder splits on (decoder.go:34). -/
def minSectorSize : Nat := 512

/-- `isTornEntry`'s split of `data`, starting at file offset `fileOff`, into chunks ending on
sector boundaries (decoder.go:175-187). -/
def sectorChunks (fileOff : Nat) : List w8 → List (List w8)
  | [] => []
  | b :: bs =>
    let n := minSectorSize - fileOff % minSectorSize
    (b :: bs).take n :: sectorChunks (fileOff + n) ((b :: bs).drop n)
termination_by l => l.length
decreasing_by
  simp only [List.length_drop, List.length_cons]
  have : fileOff % minSectorSize < minSectorSize := Nat.mod_lt _ (by decide)
  omega

/-- **`isTornEntry(data)`** with the frame at `lastValidOff = off` (decoder.go:170-203): `last`
is `len(d.brs) == 1` (the reader is in its last file); the frame's data starts at `off + 8`;
torn when some sector chunk is all zeros. -/
def isTorn (last : Bool) (off : Nat) (data : List w8) : Bool :=
  last && (sectorChunks (off + 8) data).any (fun s => s.all (· == 0#8))

/-! ## Lemmas -/

theorem framePad_lt (n : Nat) : framePad n < 8 := by unfold framePad; omega

theorem framePad_add_mod (n : Nat) : (n + framePad n) % 8 = 0 := by unfold framePad; omega

theorem encodeFrameSize_snd (n : Nat) : (encodeFrameSize n).2 = framePad n := rfl

/-! The bit facts behind the round trip, bit by bit (not `bv_decide`, whose proof rests on native
evaluation). -/

private theorem bits_hi (x : BitVec 64) (k : Nat) (hx : x.toNat < 2 ^ k) (i : Nat) (hi : k ≤ i) :
    x.getLsbD i = false := by
  rw [← BitVec.testBit_toNat]
  exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) hi))

private theorem bits_ff : ∀ j, j < 8 → (0xff#64).getLsbD j = true := by decide
private theorem bits_7 : ∀ j, j < 3 → (7#64).getLsbD j = true := by decide
private theorem bits_7' : ∀ j, j < 64 → ¬ j < 3 → (7#64).getLsbD j = false := by decide
private theorem bits_80 : ∀ j, j < 3 → (0x80#64).getLsbD j = false := by decide

private theorem fs_mask (x y : BitVec 64) (hx : x.toNat < 2 ^ 56)
    (hy : ∀ i, i < 56 → y.getLsbD i = false) :
    (x ||| y) &&& ~~~(0xff#64 <<< 56) = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft,
    hi, decide_true, Bool.true_and]
  by_cases h56 : i < 56
  · simp [h56, hy i h56]
  · rw [bits_ff (i - 56) (by omega), bits_hi x 56 hx i (by omega)]; simp [h56]

private theorem fs_bv_pad (x p : BitVec 64) (hx : x.toNat < 2 ^ 56) (hp : p.toNat < 8) :
    (x ||| ((0x80#64 ||| p) <<< 56)) &&& ~~~(0xff#64 <<< 56) = x ∧
    (x ||| ((0x80#64 ||| p) <<< 56)).slt 0#64 = true ∧
    ((x ||| ((0x80#64 ||| p) <<< 56)) >>> 56) &&& 7#64 = p := by
  refine ⟨fs_mask x _ hx (fun i hi => by simp [BitVec.getLsbD_shiftLeft, hi]), ?_, ?_⟩
  · have hm : ((0x80#64 ||| p) <<< 56).msb = true := by
      rw [BitVec.msb_eq_getLsbD_last]
      simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_or]
      simp
    rw [BitVec.slt_zero_eq_msb, BitVec.msb_or, hm, Bool.or_true]
  · apply BitVec.eq_of_getLsbD_eq
    intro j hj
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or,
      BitVec.getLsbD_shiftLeft, bits_hi x 56 hx (56 + j) (by omega)]
    by_cases h3 : j < 3
    · rw [bits_7 j h3]
      simp only [Nat.add_sub_cancel_left, bits_80 j h3]
      simp; omega
    · rw [bits_7' j hj h3, bits_hi p 3 (by omega) j (by omega)]; simp

private theorem fs_bv_nopad (x : BitVec 64) (hx : x.toNat < 2 ^ 56) :
    x &&& ~~~(0xff#64 <<< 56) = x ∧ x.slt 0#64 = false := by
  constructor
  · have := fs_mask x 0#64 hx (fun i _ => by simp)
    simpa using this
  · rw [BitVec.slt_zero_eq_msb, BitVec.msb_eq_getLsbD_last]; exact bits_hi x 56 hx 63 (by omega)

/-- **The frame size round trip** (`decodeFrameSize ∘ encodeFrameSize`) for `n < 2^56`. -/
theorem decodeFrameSize_encode (n : Nat) (h : n < 2 ^ 56) :
    decodeFrameSize (encodeFrameSize n).1 = (n, framePad n) := by
  have hxn : (BitVec.ofNat 64 n).toNat = n := by simp only [BitVec.toNat_ofNat]; omega
  have hx : (BitVec.ofNat 64 n).toNat < 2 ^ 56 := by rw [hxn]; exact h
  have hp := framePad_lt n
  unfold encodeFrameSize decodeFrameSize
  by_cases h0 : framePad n = 0
  · simp only [h0, ne_eq, not_true_eq_false, ite_false]
    obtain ⟨h1, h2⟩ := fs_bv_nopad _ hx
    rw [h1, h2]; simp [hxn]
  · have hp' : (BitVec.ofNat 64 (framePad n)).toNat < 8 := by
      simp only [BitVec.toNat_ofNat]; omega
    obtain ⟨h1, h2, h3⟩ := fs_bv_pad _ _ hx hp'
    simp only [ne_eq, h0, not_false_eq_true, ite_true, h1, h2, h3]
    simp only [uint.nat, hxn, BitVec.toNat_ofNat, Prod.mk.injEq, true_and]; omega

/-- A nonempty record's length word is not zero (so it is not read as the end, decoder.go:95). -/
theorem encodeFrameSize_ne_zero (n : Nat) (h : n < 2 ^ 56) (h0 : n ≠ 0) :
    (encodeFrameSize n).1 ≠ 0#64 := by
  intro hc
  have := decodeFrameSize_encode n h
  rw [hc] at this
  simp [decodeFrameSize] at this
  omega

@[simp] theorem frame_length (d : List w8) : (frame d).length = 8 + d.length + framePad d.length := by
  simp [frame, u64Le_length]; omega

theorem frames_nil : frames [] = [] := rfl

theorem frames_cons (d : List w8) (ds : List (List w8)) : frames (d :: ds) = frame d ++ frames ds := by
  simp [frames]

theorem frames_append (ds ds' : List (List w8)) : frames (ds ++ ds') = frames ds ++ frames ds' := by
  simp [frames]

end WalEnc
end EtcdGrove
end Perennial
