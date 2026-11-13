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

private theorem fs_bv_pad (x p : BitVec 64) (hx : x < 0x100000000000000#64) (hp : p < 8#64)
    (hp0 : p ≠ 0#64) :
    (x ||| ((0x80#64 ||| p) <<< 56)) &&& ~~~(0xff#64 <<< 56) = x ∧
    (x ||| ((0x80#64 ||| p) <<< 56)).slt 0#64 = true ∧
    ((x ||| ((0x80#64 ||| p) <<< 56)) >>> 56) &&& 7#64 = p := by
  bv_decide

private theorem fs_bv_nopad (x : BitVec 64) (hx : x < 0x100000000000000#64) :
    x &&& ~~~(0xff#64 <<< 56) = x ∧ x.slt 0#64 = false := by
  bv_decide

/-- **The frame size round trip** (`decodeFrameSize ∘ encodeFrameSize`) for `n < 2^56`. -/
theorem decodeFrameSize_encode (n : Nat) (h : n < 2 ^ 56) :
    decodeFrameSize (encodeFrameSize n).1 = (n, framePad n) := by
  have hx : BitVec.ofNat 64 n < 0x100000000000000#64 := by
    rw [BitVec.lt_def]; simp only [BitVec.toNat_ofNat]; omega
  have hxn : (BitVec.ofNat 64 n).toNat = n := by simp only [BitVec.toNat_ofNat]; omega
  have hp := framePad_lt n
  unfold encodeFrameSize decodeFrameSize
  by_cases h0 : framePad n = 0
  · simp only [h0, ne_eq, not_true_eq_false, ite_false]
    obtain ⟨h1, h2⟩ := fs_bv_nopad _ hx
    rw [h1, h2]; simp [hxn]
  · have hp' : BitVec.ofNat 64 (framePad n) < 8#64 := by
      rw [BitVec.lt_def]; simp only [BitVec.toNat_ofNat]; omega
    have hp0 : BitVec.ofNat 64 (framePad n) ≠ 0#64 := by
      intro hc; apply h0
      have := congrArg BitVec.toNat hc; simp only [BitVec.toNat_ofNat] at this; omega
    obtain ⟨h1, h2, h3⟩ := fs_bv_pad _ _ hx hp' hp0
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
