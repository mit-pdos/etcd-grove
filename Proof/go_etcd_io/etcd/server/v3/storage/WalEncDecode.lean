/-
**The WAL's decoder, as a pure function of a file's bytes** (W1 of `notes/wal-fsext-plan.md`,
§2.2-§2.3). The Go reference is the WAL at the pin (fork commit `0b50f04262d9`): `decoder.go`'s
`decodeRecord` (:88-155) and `readInt64` (:227-231), iterated by the readers' loop with their
handling of a CRC record (`ReadAll`, wal.go:523-593, :556-564; `validSnapshotEntries`, :759-766, and
`Verify`, :832-839, do the same).

The layer is generic over the codec (`WalCodec`): CRC32-Castagnoli (`crc32.Update` over
`crcTable`, which Go computes in assembly: its trusted model is stated elsewhere) and the protobuf
encoding of a `walpb.Record` (whose models are protobuf's). Only their laws (`WalCodec.Ok`) are used.

One file only (the reader in its last file: `len(d.brs) == 1`); the multi-file reader (the next
file at an end of file, decoder.go:95-103) is not modelled yet.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.WalEncFrame

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace WalEnc

/-- **A `walpb.Record` as the decoder sees it**: `GetType()`, `GetCrc()` and `Data` (a nil field
reads as zero, a nil `Data` as empty). -/
structure WalRec where
  typ : w64
  crc : w32
  data : List w8
deriving DecidableEq

/-- The record types (wal.go:39-44). -/
def metadataType : w64 := 1#64
def entryType : w64 := 2#64
def stateType : w64 := 3#64
def crcType : w64 := 4#64
def snapshotType : w64 := 5#64

/-- **The codec the WAL's bytes are written in** (parameters: their models live elsewhere).
`crc32c c p` is `crc32.Update(c, crcTable, p)` (Castagnoli; `pkg/crc`'s `Write`/`Sum32`).
`encRec r` is the bytes `proto.Marshal`/`MarshalAppend` give for the record the WAL builds for `r`
(`encode`, encoder.go:66-93); `decRec bs` is `proto.Unmarshal(bs, rec)` into a reset record
(decoder.go:82, :125), `none` on its error. -/
structure WalCodec where
  crc32c : w32 → List w8 → w32
  encRec : WalRec → List w8
  decRec : List w8 → Option WalRec

/-- **The codec's laws** (all the layer uses). `dec_enc`: `Unmarshal ∘ Marshal = id` on records whose encoding fits a frame (below `2^56`
bytes, the frame length word's 56 bits: an unbounded record has no Go encoding);
`enc_ne`: a record's encoding is not empty (its type is always set: `encode` refuses a nil type,
encoder.go:67-69, and a set field is marshalled); `crc_nil`: `crc32.Update(c, tab, nil) = c`. -/
structure WalCodec.Ok (C : WalCodec) : Prop where
  dec_enc : ∀ r, (C.encRec r).length < 2 ^ 56 → C.decRec (C.encRec r) = some r
  enc_ne : ∀ r, C.encRec r ≠ []
  crc_nil : ∀ c, C.crc32c c [] = c

/-- **Why the reader stops** (the error `Decode`, or the reader's CRC-record check, returns).
`unexpectedEOF` says which of them `errors.Is(err, io.ErrUnexpectedEOF)`. -/
inductive WalStop where
  /-- End of file, or a zero length word (preallocated space): `io.EOF` (decoder.go:95-99). -/
  | eof
  /-- 1-7 bytes left for the length word: `binary.Read`'s `io.ErrUnexpectedEOF` (:94, :104-106). -/
  | shortLen
  /-- The frame is longer than the file allows (:110-114; wraps `io.ErrUnexpectedEOF`). -/
  | tooLarge
  /-- Fewer bytes left than the frame (`io.ReadFull`, :116-124: `io.ErrUnexpectedEOF`). -/
  | shortData
  /-- `proto.Unmarshal` failed (:125-130): `io.ErrUnexpectedEOF` if `torn`, else its error. -/
  | badRec (torn : Bool)
  /-- The record's CRC is not the chain's (:133-150): wraps `io.ErrUnexpectedEOF` if `torn`, else
  `ErrCRCMismatch`. -/
  | crcErr (torn : Bool)
  /-- A CRC record whose CRC is not the chain's, the chain not zero (wal.go:557-563:
  `ErrCRCMismatch`). -/
  | crcRec
deriving DecidableEq

/-- Whether the stop's error is an `io.ErrUnexpectedEOF` (`errors.Is`). -/
def WalStop.unexpectedEOF : WalStop → Bool
  | .eof => false
  | .shortLen | .tooLarge | .shortData => true
  | .badRec t | .crcErr t => t
  | .crcRec => false

/-- One step of the reader. -/
inductive DecStep where
  | stop (s : WalStop)
  /-- A record accepted: its frame's length and the chain's CRC after it. -/
  | accept (r : WalRec) (len : Nat) (c : w32)

/-- **One `decodeRecord` call, then the reader's CRC-record check**, on the file `bs` with
`lastValidOff = off` and the decoder's CRC `c` (decoder.go:88-155, wal.go:556-564). `last`:
`len(d.brs) == 1`. The file's size (`FileInfo().Size()`, :110) is `|bs|`. The record-size limit
`recBytes > size - lastValidOff - padBytes` (signed, :110-111) is `|bs| < off + pad + rb`. A CRC
record is not checked by the decoder (:133) but by the reader against a nonzero chain, which then
takes the record's CRC (`UpdateCRC`); any other record extends the chain by its data (`Write`,
:134) and must carry the result (`Validate`, :138). -/
def decStep (C : WalCodec) (last : Bool) (bs : List w8) (off : Nat) (c : w32) : DecStep :=
  let rest := bs.drop off
  if rest.length = 0 then .stop .eof
  else if rest.length < 8 then .stop .shortLen
  else
    let l := leToU64 (rest.take 8)
    if l = 0#64 then .stop .eof
    else
      let rb := (decodeFrameSize l).1
      let pad := (decodeFrameSize l).2
      if bs.length < off + pad + rb then .stop .tooLarge
      else if rest.length < 8 + rb + pad then .stop .shortData
      else
        let data := (rest.drop 8).take (rb + pad)
        match C.decRec (data.take rb) with
        | none => .stop (.badRec (isTorn last off data))
        | some r =>
          if r.typ ≠ crcType then
            if r.crc = C.crc32c c r.data then .accept r (8 + rb + pad) (C.crc32c c r.data)
            else .stop (.crcErr (isTorn last off data))
          else if c ≠ 0#32 ∧ r.crc ≠ c then .stop .crcRec
          else .accept r (8 + rb + pad) r.crc

theorem decStep_rec_bound {C : WalCodec} {last : Bool} {bs : List w8} {off : Nat} {c : w32}
    {r : WalRec} {len : Nat} {c' : w32} (h : decStep C last bs off c = .accept r len c') :
    8 ≤ len ∧ off + len ≤ bs.length := by
  unfold decStep at h
  simp only at h
  split at h; · cases h
  split at h; · cases h
  split at h; · cases h
  split at h; · cases h
  split at h; · cases h
  rename_i h5
  simp only [Nat.not_lt, List.length_drop] at h5
  split at h; · cases h
  split at h
  · split at h <;> cases h; omega
  · split at h; · cases h
    cases h; omega

/-- What the reader returns: the records accepted, why it stopped, and `LastOffset()`/`LastCRC()`
after the last accepted record (after a CRC error the Go decoder's CRC has the bad data written
into it, and after the reader's CRC-record check fails its offset is past that record: the readers
use them only after `io.EOF`). -/
structure DecOut where
  recs : List WalRec
  stop : WalStop
  off : Nat
  crc : w32

/-- **The reader's loop from `lastValidOff = off` and CRC `c`** (`for err = decoder.Decode(rec);
err == nil; ...`, wal.go:523). -/
def walDecodeFrom (C : WalCodec) (last : Bool) (bs : List w8) (off : Nat) (c : w32) : DecOut :=
  match _h : decStep C last bs off c with
  | .stop s => ⟨[], s, off, c⟩
  | .accept r len c' =>
    let o := walDecodeFrom C last bs (off + len) c'
    { o with recs := r :: o.recs }
termination_by bs.length - off
decreasing_by have := decStep_rec_bound _h; omega

/-- **`walDecode bs`: the reader on one file `bs`** (`NewDecoder`: offset 0, CRC
`crc.New(0, crcTable)`, decoder.go:60-74). -/
def walDecode (C : WalCodec) (bs : List w8) : DecOut := walDecodeFrom C true bs 0 0#32

theorem walDecodeFrom_unfold (C : WalCodec) (last : Bool) (bs : List w8) (off : Nat) (c : w32) :
    walDecodeFrom C last bs off c =
      match decStep C last bs off c with
      | .stop s => ⟨[], s, off, c⟩
      | .accept r len c' =>
        let o := walDecodeFrom C last bs (off + len) c'
        { o with recs := r :: o.recs } := by
  rw [walDecodeFrom]; split <;> simp_all

/-! ## The CRC chain -/

/-- The chain's CRC after the record `r` (the reader's: a CRC record sets it, any other extends it
by the record's data). -/
def crcNext (C : WalCodec) (c : w32) (r : WalRec) : w32 :=
  if r.typ ≠ crcType then C.crc32c c r.data else r.crc

/-- The reader accepts `r`'s CRC at chain value `c`. -/
def CrcOk (C : WalCodec) (c : w32) (r : WalRec) : Prop :=
  if r.typ ≠ crcType then r.crc = C.crc32c c r.data else (c = 0#32 ∨ r.crc = c)

/-- The records' CRCs are a chain from `c`. -/
def ChainOk (C : WalCodec) : w32 → List WalRec → Prop
  | _, [] => True
  | c, r :: rs => CrcOk C c r ∧ ChainOk C (crcNext C c r) rs

/-- The chain's value after the records. -/
def chainEnd (C : WalCodec) : w32 → List WalRec → w32
  | c, [] => c
  | c, r :: rs => chainEnd C (crcNext C c r) rs

theorem chainOk_append (C : WalCodec) (c : w32) (xs ys : List WalRec) :
    ChainOk C c (xs ++ ys) ↔ ChainOk C c xs ∧ ChainOk C (chainEnd C c xs) ys := by
  induction xs generalizing c with
  | nil => simp [ChainOk, chainEnd]
  | cons x xs ih => simp only [List.cons_append, ChainOk, chainEnd, ih, and_assoc]

theorem chainEnd_append (C : WalCodec) (c : w32) (xs ys : List WalRec) :
    chainEnd C c (xs ++ ys) = chainEnd C (chainEnd C c xs) ys := by
  induction xs generalizing c with
  | nil => rfl
  | cons x xs ih => exact ih _

/-- The records fit a frame (their encodings are shorter than `2^56`, the length word's field). -/
def RecsFit (C : WalCodec) (rs : List WalRec) : Prop := ∀ r ∈ rs, (C.encRec r).length < 2 ^ 56

/-- The frames of the records, as the encoder writes them. -/
def recFrames (C : WalCodec) (rs : List WalRec) : List w8 := frames (rs.map C.encRec)

theorem recFrames_nil (C : WalCodec) : recFrames C [] = [] := rfl

theorem recFrames_cons (C : WalCodec) (r : WalRec) (rs : List WalRec) :
    recFrames C (r :: rs) = frame (C.encRec r) ++ recFrames C rs := by
  simp [recFrames, frames_cons]

theorem recFrames_append (C : WalCodec) (xs ys : List WalRec) :
    recFrames C (xs ++ ys) = recFrames C xs ++ recFrames C ys := by
  simp [recFrames, frames_append]

/-! ## Decoding what the encoder wrote -/

/-- **A frame the encoder wrote is accepted** (decoder.go:88-155 on `frame (encRec r)`), when its
CRC is the chain's. -/
theorem decStep_frame {C : WalCodec} (hC : C.Ok) (last : Bool) {bs : List w8} {off : Nat}
    {c : w32} {r : WalRec} {rest : List w8} (hfit : (C.encRec r).length < 2 ^ 56)
    (hbs : bs.drop off = frame (C.encRec r) ++ rest) (hcrc : CrcOk C c r) :
    decStep C last bs off c = .accept r (frame (C.encRec r)).length (crcNext C c r) := by
  have hn0 : (C.encRec r).length ≠ 0 := by
    intro h; exact hC.enc_ne r (List.length_eq_zero_iff.mp h)
  have hp := framePad_lt (C.encRec r).length
  have hlen : (bs.drop off).length = 8 + (C.encRec r).length + framePad (C.encRec r).length +
      rest.length := by
    rw [hbs, List.length_append, frame_length]
  have hbsl := List.length_drop (l := bs) (i := off)
  have htake : (bs.drop off).take 8 = u64Le (encodeFrameSize (C.encRec r).length).1 := by
    rw [hbs]; simp only [frame, List.append_assoc]
    exact List.take_left' (u64Le_length _)
  have hdrop : (bs.drop off).drop 8 = C.encRec r ++ List.replicate (framePad (C.encRec r).length) (0#8)
      ++ rest := by
    rw [hbs]; simp only [frame, List.append_assoc]
    exact List.drop_left' (u64Le_length _)
  have hdata : ((bs.drop off).drop 8).take ((C.encRec r).length + framePad (C.encRec r).length) =
      C.encRec r ++ List.replicate (framePad (C.encRec r).length) (0#8) := by
    rw [hdrop]; exact List.take_left' (by simp)
  have hdata' : (C.encRec r ++ List.replicate (framePad (C.encRec r).length) (0#8)).take
      (C.encRec r).length = C.encRec r := List.take_left' rfl
  have hfs := decodeFrameSize_encode _ hfit
  have hne := encodeFrameSize_ne_zero _ hfit hn0
  unfold decStep
  simp only [htake, u64Le_to_word, hfs, hdata, hdata', hC.dec_enc r hfit]
  rw [frame_length]
  unfold CrcOk at hcrc
  unfold crcNext
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right hne, ite_eq_right (by omega), ite_eq_right (by omega)]
  by_cases ht : r.typ ≠ crcType
  · rw [ite_eq_left ht] at hcrc ⊢; rw [ite_eq_left hcrc, ite_eq_left ht]
  · rw [ite_eq_right ht] at hcrc ⊢; rw [ite_eq_right ht, ite_eq_right (by intro ⟨h1, h2⟩; rcases hcrc with h | h <;> contradiction)]

/-- **The encoder's frames decode to its records**, then the reader goes on after them. -/
theorem walDecodeFrom_frames {C : WalCodec} (hC : C.Ok) {last : Bool} {bs : List w8} (rs : List WalRec) :
    ∀ {off : Nat} {c : w32} {rest : List w8}, RecsFit C rs → ChainOk C c rs →
    bs.drop off = recFrames C rs ++ rest →
    walDecodeFrom C last bs off c =
      let o := walDecodeFrom C last bs (off + (recFrames C rs).length) (chainEnd C c rs)
      { o with recs := rs ++ o.recs } := by
  induction rs with
  | nil => intro off c rest _ _ _; simp [recFrames_nil, chainEnd]
  | cons r rs ih =>
    intro off c rest hfit hch hbs
    rw [recFrames_cons, List.append_assoc] at hbs
    have hstep := decStep_frame hC last (hfit r (by simp)) hbs hch.1
    rw [walDecodeFrom_unfold, hstep]
    have hbs' : bs.drop (off + (frame (C.encRec r)).length) = recFrames C rs ++ rest := by
      rw [← List.drop_drop, hbs]
      exact List.drop_left' rfl
    simp only
    rw [ih (fun r' h => hfit r' (by simp [h])) hch.2 hbs']
    simp [recFrames_cons, chainEnd, Nat.add_assoc]

/-- Zeros, or nothing, at the offset: the step reads the end. -/
theorem decStep_zeros (C : WalCodec) (last : Bool) {bs : List w8} {off z : Nat} {c : w32}
    (hz : z = 0 ∨ 8 ≤ z) (hbs : bs.drop off = List.replicate z (0#8)) :
    decStep C last bs off c = .stop .eof := by
  unfold decStep
  simp only [hbs, List.length_replicate]
  rcases hz with rfl | hz
  · simp
  · have h8 : List.take 8 (List.replicate z (0#8)) = u64Le (W64 0) := by
      rw [List.take_replicate, u64Le_0, Nat.min_eq_left hz]; rfl
    rw [ite_eq_right (by omega), ite_eq_right (by omega), h8, u64Le_to_word, ite_eq_left (by decide)]

/-- **Zeros, or nothing, read as the end** (decoder.go:95: a zero length word; the end of the
file). Fewer than 8 zeros would be `shortLen`: the WAL's frames and preallocation keep 8-byte
alignment. -/
theorem walDecodeFrom_zeros (C : WalCodec) {last : Bool} {bs : List w8} {off z : Nat} {c : w32}
    (hz : z = 0 ∨ 8 ≤ z) (hbs : bs.drop off = List.replicate z (0#8)) :
    walDecodeFrom C last bs off c = ⟨[], .eof, off, c⟩ := by
  rw [walDecodeFrom_unfold, decStep_zeros C last hz hbs]

/-- An accepted step reads only its frame: bytes appended after the file change nothing. -/
theorem decStep_append {C : WalCodec} {last : Bool} {img : List w8} {off : Nat} {c : w32}
    {r : WalRec} {len : Nat} {c' : w32} (zs : List w8)
    (h : decStep C last img off c = .accept r len c') :
    decStep C last (img ++ zs) off c = .accept r len c' := by
  have hb := decStep_rec_bound h
  have hr : (img ++ zs).drop off = img.drop off ++ zs := List.drop_append_of_le_length (by omega)
  have hl : (img.drop off).length = img.length - off := List.length_drop
  unfold decStep at h ⊢
  simp only at h ⊢
  rw [hr]
  split at h; · cases h
  split at h; · cases h
  rename_i h1 h2
  have ht8 : (img.drop off ++ zs).take 8 = (img.drop off).take 8 :=
    List.take_append_of_le_length (by omega)
  rw [ht8]
  split at h; · cases h
  rename_i h3
  split at h; · cases h
  rename_i h4
  split at h; · cases h
  rename_i h5
  have hd8 : (img.drop off ++ zs).drop 8 = (img.drop off).drop 8 ++ zs :=
    List.drop_append_of_le_length (by omega)
  have hd : ((img.drop off ++ zs).drop 8).take
        ((decodeFrameSize (leToU64 ((img.drop off).take 8))).1 +
         (decodeFrameSize (leToU64 ((img.drop off).take 8))).2) =
      ((img.drop off).drop 8).take
        ((decodeFrameSize (leToU64 ((img.drop off).take 8))).1 +
         (decodeFrameSize (leToU64 ((img.drop off).take 8))).2) := by
    rw [hd8]; exact List.take_append_of_le_length (by simp only [List.length_drop]; omega)
  rw [ite_eq_right (by simp only [List.length_append]; omega),
    ite_eq_right (by simp only [List.length_append]; omega), ite_eq_right h3,
    ite_eq_right (by simp only [List.length_append]; omega),
    ite_eq_right (by simp only [List.length_append]; omega), hd]
  exact h

/-- A step that read the end (within the file) still reads it with zeros appended. -/
theorem decStep_append_eof {C : WalCodec} {last : Bool} {img : List w8} {off z : Nat} {c : w32}
    (hz : z = 0 ∨ 8 ≤ z) (hoff : off ≤ img.length) (h : decStep C last img off c = .stop .eof) :
    decStep C last (img ++ List.replicate z (0#8)) off c = .stop .eof := by
  have hr : (img ++ List.replicate z (0#8)).drop off = img.drop off ++ List.replicate z (0#8) :=
    List.drop_append_of_le_length hoff
  by_cases h0 : (img.drop off).length = 0
  · apply decStep_zeros C last hz
    rw [hr, List.eq_nil_of_length_eq_zero h0, List.nil_append]
  · unfold decStep at h ⊢
    simp only at h ⊢
    rw [hr, ite_eq_right (by simp only [List.length_append]; omega)]
    rw [ite_eq_right h0] at h
    have h8 : ¬ (img.drop off).length < 8 := by
      intro h8; rw [ite_eq_left h8] at h; cases h
    rw [ite_eq_right h8] at h
    rw [ite_eq_right (by simp only [List.length_append]; omega),
      List.take_append_of_le_length (by omega)]
    by_cases hl : leToU64 ((img.drop off).take 8) = 0#64
    · rw [ite_eq_left hl]
    · exfalso
      rw [ite_eq_right hl] at h
      split at h; · cases h
      split at h; · cases h
      split at h
      · cases h
      · split at h
        · split at h <;> cases h
        · split at h <;> cases h

theorem walDecodeFrom_append_zeros (C : WalCodec) {last : Bool} {img : List w8} {z : Nat} (hz : z = 0 ∨ 8 ≤ z) :
    ∀ n off c, img.length - off = n → off ≤ img.length →
    (walDecodeFrom C last img off c).stop = .eof →
    (walDecodeFrom C last (img ++ List.replicate z (0#8)) off c).recs = (walDecodeFrom C last img off c).recs ∧
    (walDecodeFrom C last (img ++ List.replicate z (0#8)) off c).stop = .eof := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro off c hn hoff heof
    rw [walDecodeFrom_unfold] at heof
    rw [walDecodeFrom_unfold (bs := img), walDecodeFrom_unfold (bs := img ++ _)]
    cases hs : decStep C last img off c with
    | stop s =>
      rw [hs] at heof
      simp only at heof
      subst heof
      rw [decStep_append_eof hz hoff hs]
      exact ⟨rfl, rfl⟩
    | accept r len c' =>
      rw [hs] at heof
      rw [decStep_append _ hs]
      have hb := decStep_rec_bound hs
      have := ih (img.length - (off + len)) (by omega) (off + len) c' rfl (by omega) heof
      simp only [this.1, this.2, and_self]

/-! ## Images that are not what was written -/

/-- **No collision** (an abstract hypothesis, discharged from the crash model's W1): wherever the
reader, having accepted the first records `xs` of the intended records `rs = xs ++ ys`, accepts a
frame in the image `img`, the intended stream has a frame there (`ys = r :: _`) and the image holds
exactly its bytes. That is, a frame whose bytes differ from the intended frame at that position
(or that lies past the intended records) fails the reader's checks. -/
def NoCollisionFrom (C : WalCodec) (c0 : w32) (rs : List WalRec) (img : List w8) : Prop :=
  ∀ xs ys r len c', xs ++ ys = rs →
    decStep C true img (recFrames C xs).length (chainEnd C c0 xs) = .accept r len c' →
    ∃ r' ys', ys = r' :: ys' ∧
      (img.drop (recFrames C xs).length).take (frame (C.encRec r')).length = frame (C.encRec r')

/-- **(b) The reader accepts a prefix of the intended records**, on any image without collision. -/
theorem walDecodeFrom_prefix {C : WalCodec} (hC : C.Ok) {c0 : w32} {rs : List WalRec}
    {img : List w8} (hfit : RecsFit C rs) (hchain : ChainOk C c0 rs)
    (hnc : NoCollisionFrom C c0 rs img) :
    (walDecodeFrom C true img 0 c0).recs <+: rs := by
  have key : ∀ ys xs, xs ++ ys = rs →
      (walDecodeFrom C true img (recFrames C xs).length (chainEnd C c0 xs)).recs <+: ys := by
    intro ys
    induction ys with
    | nil =>
      intro xs hxs
      rw [walDecodeFrom_unfold]
      split
      · exact List.nil_prefix
      · rename_i r len c' h
        obtain ⟨r', ys', hys, _⟩ := hnc xs [] r len c' hxs h
        cases hys
    | cons y ys ih =>
      intro xs hxs
      rw [walDecodeFrom_unfold]
      split
      · exact List.nil_prefix
      · rename_i r len c' h
        obtain ⟨r', ys', hys, hwin⟩ := hnc xs (y :: ys) r len c' hxs h
        injection hys with hy _
        rw [← hy] at hwin
        have hbs : img.drop (recFrames C xs).length = frame (C.encRec y) ++
            (img.drop (recFrames C xs).length).drop (frame (C.encRec y)).length := by
          have e := List.take_append_drop (frame (C.encRec y)).length
            (img.drop (recFrames C xs).length)
          rw [hwin] at e
          exact e.symm
        have hch : ChainOk C (chainEnd C c0 xs) (y :: ys) :=
          ((chainOk_append C c0 xs (y :: ys)).mp (hxs ▸ hchain)).2
        have hst := decStep_frame hC true (hfit y (by rw [← hxs]; simp)) hbs hch.1
        rw [h] at hst
        injection hst with h1 h2 h3
        subst h1 h2 h3
        have := ih (xs ++ [r]) (by rw [List.append_assoc]; exact hxs)
        rw [recFrames_append, chainEnd_append] at this
        simp only [recFrames_cons, recFrames_nil, List.append_nil, chainEnd, List.length_append]
          at this
        exact List.cons_prefix_cons.mpr ⟨rfl, this⟩
  have := key rs [] rfl
  simp only [recFrames_nil, List.length_nil, chainEnd] at this
  exact this

/-- **What the image starts with is accepted**: an image whose first bytes are the frames of `xs`
decodes to `xs` and more. -/
theorem walDecodeFrom_of_prefix {C : WalCodec} (hC : C.Ok) (last : Bool) {c0 : w32}
    {xs : List WalRec} {img : List w8}
    (hfit : RecsFit C xs) (hchain : ChainOk C c0 xs) (hpre : recFrames C xs <+: img) :
    xs <+: (walDecodeFrom C last img 0 c0).recs := by
  obtain ⟨rest, hrest⟩ := hpre
  have h := walDecodeFrom_frames hC (last := last) (bs := img) xs (off := 0) (c := c0) (rest := rest) hfit hchain
    (by rw [List.drop_zero, hrest])
  rw [h]
  exact List.prefix_append _ _

/-- No collision for the reader of one file from CRC 0. -/
abbrev NoCollision (C : WalCodec) (rs : List WalRec) (img : List w8) : Prop :=
  NoCollisionFrom C 0#32 rs img

/-- **(b) The reader accepts a prefix of the intended records**, on any image without collision. -/
theorem walDecode_prefix {C : WalCodec} (hC : C.Ok) {rs : List WalRec} {img : List w8}
    (hfit : RecsFit C rs) (hchain : ChainOk C 0#32 rs) (hnc : NoCollision C rs img) :
    (walDecode C img).recs <+: rs := walDecodeFrom_prefix hC hfit hchain hnc

/-- **What the image starts with is accepted**: an image whose first bytes are the frames of `xs`
decodes to `xs` and more. -/
theorem walDecode_of_prefix {C : WalCodec} (hC : C.Ok) {xs : List WalRec} {img : List w8}
    (hfit : RecsFit C xs) (hchain : ChainOk C 0#32 xs) (hpre : recFrames C xs <+: img) :
    xs <+: (walDecode C img).recs := walDecodeFrom_of_prefix hC true hfit hchain hpre

/-- **(d) Appending zeros changes nothing after an end of file**: a reader that stopped at `io.EOF`
reads the same records from the image followed by preallocated zeros. -/
theorem walDecode_append_zeros (C : WalCodec) {img : List w8} {z : Nat} (hz : z = 0 ∨ 8 ≤ z)
    (heof : (walDecode C img).stop = .eof) :
    (walDecode C (img ++ List.replicate z (0#8))).recs = (walDecode C img).recs ∧
    (walDecode C (img ++ List.replicate z (0#8))).stop = .eof :=
  walDecodeFrom_append_zeros C hz _ 0 0#32 rfl (Nat.zero_le _) heof

end WalEnc
end EtcdGrove
end Perennial
