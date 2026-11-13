/-
**The Go decoder's own step, and the readers' loop over it** (pure; W3a of
`notes/wal-fsext-plan.md`). The Go reference is the WAL at the pin with the local fork fix
(`notes/wal-fsext-fork/0001-*.patch`): `decoder.decodeRecord` (decoder.go:88-158) and the readers'
loop around `Decode` (`ReadAll`, wal.go:523-593, its CRC record at :556-564; `validSnapshotEntries`
and `Verify` do the same).

`decStep`/`walDecodeFrom`/`walDecodeFiles` (`WalEncDecode.lean`, `WalEncFiles.lean`) model *the
reader*: the decoder's step followed by the reader's handling of a CRC record. The Go decoder alone
differs on a CRC record: it checks nothing and leaves its CRC as it was (decoder.go:132-151); the
reader then checks it against `LastCRC()` and calls `UpdateCRC(rec.Crc)`. And on a CRC mismatch the
Go decoder's CRC already has the record's data written into it (:134). This file states the
decoder's step as Go has it (`decRecStep`, `goDecode`: the state is the files left, `lastValidOff`
and the CRC) and proves that the readers' loop over it computes `walDecodeFiles`
(`rdRest_*`, `readerLoop_eq`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.WalEncFiles

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace WalEnc

/-- What one `decodeRecord` call does in one file (decoder.go:94-158, the file not dropped). -/
inductive RecStep where
  /-- End of file or a zero length word (:95): the file is dropped. -/
  | eof
  /-- An error; the decoder's CRC is then `c` (changed only by a CRC mismatch, :134). -/
  | stop (s : WalStop) (c : w32)
  /-- A record accepted: its frame's length and the decoder's CRC after it. -/
  | accept (r : WalRec) (len : Nat) (c : w32)

/-- **The Go decoder's step in the file `bs`** at `lastValidOff = off`, CRC `c` (decoder.go:94-158;
`last`: `len(d.brs) == 1`). As `decStep`, but a CRC record is accepted unchecked with the CRC left
as it is, and a CRC mismatch leaves the CRC with the data written into it. -/
def decRecStep (C : WalCodec) (last : Bool) (bs : List w8) (off : Nat) (c : w32) : RecStep :=
  let rest := bs.drop off
  if rest.length = 0 then .eof
  else if rest.length < 8 then .stop .shortLen c
  else
    let l := leToU64 (rest.take 8)
    if l = 0#64 then .eof
    else
      let rb := (decodeFrameSize l).1
      let pad := (decodeFrameSize l).2
      if bs.length < off + pad + rb then .stop .tooLarge c
      else if rest.length < 8 + rb + pad then .stop .shortData c
      else
        let data := (rest.drop 8).take (rb + pad)
        match C.decRec (data.take rb) with
        | none => .stop (.badRec (isTorn last off data)) c
        | some r =>
          if r.typ ≠ crcType then
            if r.crc = C.crc32c c r.data then .accept r (8 + rb + pad) (C.crc32c c r.data)
            else .stop (.crcErr (isTorn last off data)) (C.crc32c c r.data)
          else .accept r (8 + rb + pad) c

/-- What a `Decode` call returns, and the decoder's state after it: the files left (`d.brs`'s
contents, the first being read), `lastValidOff` and the CRC. -/
inductive GoDec where
  | ok (r : WalRec) (fs : List (List w8)) (off : Nat) (c : w32)
  | stop (s : WalStop) (fs : List (List w8)) (off : Nat) (c : w32)

/-- **`decodeRecord` on the decoder `(fs, off, c)`** (decoder.go:88-158): no file left, `io.EOF`;
the end of the first file drops it and goes on in the next from offset 0 (:95-103), but the end of
the last file leaves `lastValidOff` as it was. -/
def goDecode (C : WalCodec) : List (List w8) → Nat → w32 → GoDec
  | [], off, c => .stop .eof [] off c
  | f :: fs, off, c =>
    match decRecStep C fs.isEmpty f off c with
    | .eof =>
      match fs with
      | [] => .stop .eof [] off c
      | g :: gs => goDecode C (g :: gs) 0 c
    | .stop s c' => .stop s (f :: fs) off c'
    | .accept r len c' => .ok r (f :: fs) (off + len) c'

/-- The reader's CRC check of an accepted CRC record (wal.go:556-564): it fails when the decoder's
CRC `c` (`LastCRC()`) is not zero and differs from the record's. -/
def crcRecBad (c : w32) (r : WalRec) : Prop := c ≠ 0#32 ∧ r.crc ≠ c

instance (c : w32) (r : WalRec) : Decidable (crcRecBad c r) := by unfold crcRecBad; infer_instance

/-- The decoder's CRC after the reader handled the record `r` (`UpdateCRC(rec.Crc)` for a CRC
record, wal.go:564). -/
def rdCrc (c : w32) (r : WalRec) : w32 := if r.typ = crcType then r.crc else c

/-- **What the reader reads from the decoder state `(fs, off, c)` on**: the rest of
`walDecodeFiles`, from the offset `off` in the first file. -/
def rdRest (C : WalCodec) : List (List w8) → Nat → w32 → DecOut
  | [], off, c => ⟨[], .eof, off, c⟩
  | [f], off, c => walDecodeFrom C true f off c
  | f :: g :: fs, off, c =>
    let o := walDecodeFrom C false f off c
    if o.stop = .eof then
      let o' := walDecodeFiles C (g :: fs) o.crc
      { o' with recs := o.recs ++ o'.recs }
    else o

/-- A fresh decoder (`NewDecoder(rs...)`, offset 0, CRC 0) reads `walDecodeFiles`. -/
theorem rdRest_start (C : WalCodec) (fs : List (List w8)) (c : w32) :
    rdRest C fs 0 c = walDecodeFiles C fs c := by
  rcases fs with _ | ⟨f, _ | ⟨g, fs⟩⟩ <;> rfl

theorem walDecodeFiles_cons_cons (C : WalCodec) (f g : List w8) (fs : List (List w8)) (c : w32) :
    walDecodeFiles C (f :: g :: fs) c =
      let o := walDecodeFrom C false f 0 c
      if o.stop = .eof then
        let o' := walDecodeFiles C (g :: fs) o.crc
        { o' with recs := o.recs ++ o'.recs }
      else o := rfl

/-- `decStep` is the decoder's step then the reader's CRC-record check. -/
theorem decStep_eq (C : WalCodec) (last : Bool) (bs : List w8) (off : Nat) (c : w32) :
    decStep C last bs off c =
      match decRecStep C last bs off c with
      | .eof => .stop .eof
      | .stop s _ => .stop s
      | .accept r len c' =>
        if r.typ = crcType then
          (if crcRecBad c r then .stop .crcRec else .accept r len r.crc)
        else .accept r len c' := by
  unfold decStep decRecStep crcRecBad
  simp only
  split; · rfl
  split; · rfl
  split; · rfl
  split; · rfl
  split; · rfl
  split
  · rename_i hdec; simp only [hdec]
  · rename_i r hdec
    simp only [hdec]
    by_cases ht : r.typ = crcType
    · simp only [ht, ne_eq, not_true_eq_false, ite_false, ite_true]
    · simp only [ht, ne_eq, not_false_eq_true, ite_true]
      split <;> (dsimp only; try simp [ht])

/-- `rdRest` on a first file, by the reader's step there. -/
theorem rdRest_cons (C : WalCodec) (f : List w8) (fs : List (List w8)) (off : Nat) (c : w32) :
    rdRest C (f :: fs) off c =
      match decStep C fs.isEmpty f off c with
      | .stop s => if s = .eof ∧ fs ≠ [] then rdRest C fs 0 c else ⟨[], s, off, c⟩
      | .accept r len c' =>
        let o := rdRest C (f :: fs) (off + len) c'
        { o with recs := r :: o.recs } := by
  rcases fs with _ | ⟨g, gs⟩
  · rw [show rdRest C [f] off c = walDecodeFrom C true f off c from rfl, walDecodeFrom_unfold]
    simp only [List.isEmpty_nil]
    cases decStep C true f off c with
    | stop s => simp
    | accept r len c' => rfl
  · simp only [List.isEmpty_cons]
    rw [rdRest.eq_3, walDecodeFrom_unfold C false f off c]
    cases decStep C false f off c with
    | stop s =>
      by_cases hs : s = .eof
      · subst hs; simp [rdRest_start]
      · simp [hs]
    | accept r len c' =>
      simp only [rdRest.eq_3]
      split <;> simp

/-- The end of a file that is not the last: the reader goes on in the next from offset 0. -/
theorem rdRest_next {C : WalCodec} {f : List w8} {fs : List (List w8)} {off : Nat} {c : w32}
    (hfs : fs ≠ []) (h : decRecStep C fs.isEmpty f off c = .eof) :
    rdRest C (f :: fs) off c = rdRest C fs 0 c := by
  rw [rdRest_cons, decStep_eq, h]
  simp [hfs]

/-- The decoder leaves its CRC as it is on a CRC record. -/
theorem decRecStep_crc {C : WalCodec} {last : Bool} {bs : List w8} {off : Nat} {c c' : w32}
    {r : WalRec} {len : Nat} (h : decRecStep C last bs off c = .accept r len c')
    (ht : r.typ = crcType) : c' = c := by
  unfold decRecStep at h
  simp only at h
  split at h; · cases h
  split at h; · cases h
  split at h; · cases h
  split at h; · cases h
  split at h; · cases h
  split at h
  · cases h
  · split at h
    · rename_i hne
      split at h
      · cases h; exact absurd ht hne
      · cases h
    · cases h; rfl

/-- **The loop lemma, a record step**: a `Decode` returning the record `r` (the decoder's CRC then
`c'`, `LastCRC()`), which the reader accepts (not a CRC record whose CRC it rejects), reads `r`
then what the reader reads from the new state (its CRC updated for a CRC record). -/
theorem rdRest_ok {C : WalCodec} {fs fs' : List (List w8)} {off off' : Nat} {c c' : w32}
    {r : WalRec} (h : goDecode C fs off c = .ok r fs' off' c')
    (hok : ¬ (r.typ = crcType ∧ crcRecBad c' r)) :
    rdRest C fs off c = { rdRest C fs' off' (rdCrc c' r) with
      recs := r :: (rdRest C fs' off' (rdCrc c' r)).recs } := by
  induction fs generalizing off c with
  | nil => simp [goDecode] at h
  | cons f fs ih =>
    unfold goDecode at h
    split at h
    · rename_i hs
      rcases fs with _ | ⟨g, gs⟩
      · cases h
      · rw [rdRest_next (by simp) hs]
        exact ih h
    · cases h
    · rename_i r0 len c0 hs
      injection h with h1 h2 h3 h4
      subst r0 fs' off' c0
      rw [rdRest_cons, decStep_eq, hs]
      by_cases ht : r.typ = crcType
      · have := decRecStep_crc hs ht
        subst this
        have hb : ¬ crcRecBad c' r := fun hb => hok ⟨ht, hb⟩
        have hc : rdCrc c' r = r.crc := by simp [rdCrc, ht]
        simp only [ht, hb, ite_true, ite_false, hc]
      · have hc : rdCrc c' r = c' := by simp [rdCrc, ht]
        simp only [ht, ite_false, hc]

/-- **The loop lemma, a CRC record the reader rejects** (wal.go:557-563): the reader stops there
with `ErrCRCMismatch`, having read nothing more. -/
theorem rdRest_crcRec {C : WalCodec} {fs fs' : List (List w8)} {off off' : Nat} {c c' : w32}
    {r : WalRec} (h : goDecode C fs off c = .ok r fs' off' c')
    (hbad : r.typ = crcType ∧ crcRecBad c' r) :
    (rdRest C fs off c).recs = [] ∧ (rdRest C fs off c).stop = .crcRec := by
  induction fs generalizing off c with
  | nil => simp [goDecode] at h
  | cons f fs ih =>
    unfold goDecode at h
    split at h
    · rename_i hs
      rcases fs with _ | ⟨g, gs⟩
      · cases h
      · rw [rdRest_next (by simp) hs]
        exact ih h
    · cases h
    · rename_i r0 len c0 hs
      injection h with h1 h2 h3 h4
      subst r0 fs' off' c0
      have := decRecStep_crc hs hbad.1
      subst this
      rw [rdRest_cons, decStep_eq, hs]
      simp [hbad.1, hbad.2]

/-- `decRecStep` stops with `eof` only by `.eof`, and an error but a CRC mismatch leaves the CRC. -/
theorem decRecStep_stop {C : WalCodec} {last : Bool} {bs : List w8} {off : Nat} {c c' : w32}
    {s : WalStop} (h : decRecStep C last bs off c = .stop s c') :
    s ≠ .eof ∧ ((∀ t, s ≠ .crcErr t) → c' = c) := by
  unfold decRecStep at h
  simp only at h
  split at h; · cases h
  split at h; · cases h; exact ⟨by decide, fun _ => rfl⟩
  split at h; · cases h
  split at h; · cases h; exact ⟨by decide, fun _ => rfl⟩
  split at h; · cases h; exact ⟨by decide, fun _ => rfl⟩
  split at h
  · cases h; exact ⟨by simp, fun _ => rfl⟩
  · split at h
    · split at h
      · cases h
      · cases h; exact ⟨by simp, fun ht => absurd rfl (ht _)⟩
    · cases h

/-- **The loop lemma, an error**: a `Decode` returning an error (the stop `s`) ends the reader
there with `s` and no more records; but for a CRC mismatch (whose CRC took the bad data) the
reader's offset and CRC are the decoder's (`LastOffset()`, `LastCRC()`). -/
theorem rdRest_stop {C : WalCodec} {fs fs' : List (List w8)} {off off' : Nat} {c c' : w32}
    {s : WalStop} (h : goDecode C fs off c = .stop s fs' off' c') :
    (rdRest C fs off c).recs = [] ∧ (rdRest C fs off c).stop = s ∧
    ((∀ t, s ≠ .crcErr t) → (rdRest C fs off c).off = off' ∧ (rdRest C fs off c).crc = c') := by
  induction fs generalizing off c with
  | nil =>
    injection h with h1 h2 h3 h4
    subst s fs' off' c'
    exact ⟨rfl, rfl, fun _ => ⟨rfl, rfl⟩⟩
  | cons f fs ih =>
    unfold goDecode at h
    split at h
    · rename_i hs
      rcases fs with _ | ⟨g, gs⟩
      · injection h with h1 h2 h3 h4
        subst s fs' off' c'
        rw [rdRest_cons, decStep_eq, hs]
        exact ⟨rfl, rfl, fun _ => ⟨rfl, rfl⟩⟩
      · rw [rdRest_next (by simp) hs]
        exact ih h
    · rename_i s0 c0 hs
      injection h with h1 h2 h3 h4
      subst s0 fs' off' c0
      obtain ⟨hne, hc⟩ := decRecStep_stop hs
      rw [rdRest_cons, decStep_eq, hs]
      simp only [hne, false_and, ite_false, true_and]
      intro ht; simp [hc ht]
    · cases h


/-! ## A failed `proto.Unmarshal`

`decRecStep` (and `walDecodeFrom`) take `proto.Unmarshal` to be the canonical decoding `C.decRec`.
Its trusted spec (`proto.UnmarshalPb.spec`) says less: a success gives the canonical decoding, but
it may fail on any bytes that are not the encoding of a valid record (D2). So the Go decoder may
also stop with `badRec` at a frame whose bytes `decRec` decodes: `GoFail` (the weaker model of
W3a, 2026-11-13). Only bytes the encoder never wrote can fail (`UFail`), so a frame the encoder
wrote is read as `decRecStep` says. -/

/-- `proto.Unmarshal` may fail on the bytes `u`: they are no record's encoding (D2). -/
def UFail (C : WalCodec) (u : List w8) : Prop := ∀ r, u ≠ C.encRec r

/-- **The frame `decodeRecord` hands to `proto.Unmarshal`** in the file `bs` at `lastValidOff =
off` (decoder.go:104-125): its data (record and padding) and the record's length, when the step
gets that far. -/
def decFrame (bs : List w8) (off : Nat) : Option (List w8 × Nat) :=
  let rest := bs.drop off
  if rest.length = 0 then none
  else if rest.length < 8 then none
  else
    let l := leToU64 (rest.take 8)
    if l = 0#64 then none
    else
      let rb := (decodeFrameSize l).1
      let pad := (decodeFrameSize l).2
      if bs.length < off + pad + rb then none
      else if rest.length < 8 + rb + pad then none
      else some ((rest.drop 8).take (rb + pad), rb)

/-- **`decodeRecord`'s `proto.Unmarshal` fails in the file `bs`** (decoder.go:125-130): the stop
`s` it returns. -/
def RecFail (C : WalCodec) (last : Bool) (bs : List w8) (off : Nat) (s : WalStop) : Prop :=
  ∃ data rb, decFrame bs off = some (data, rb) ∧ UFail C (data.take rb) ∧
    s = .badRec (isTorn last off data)

/-- **`decodeRecord` on the decoder `(fs, off, c)` stops on a failed `proto.Unmarshal`**: the
stop and the decoder's state after it (`goDecode`'s, but the `Unmarshal` failed): the files at
whose end it is are dropped first (:95-103). -/
inductive GoFail (C : WalCodec) :
    List (List w8) → Nat → w32 → WalStop → List (List w8) → Nat → w32 → Prop where
  | here {f fs off c s} : RecFail C fs.isEmpty f off s → GoFail C (f :: fs) off c s (f :: fs) off c
  | next {f g gs off c s fs' off' c'} : decRecStep C false f off c = .eof →
      GoFail C (g :: gs) 0 c s fs' off' c' → GoFail C (f :: g :: gs) off c s fs' off' c'

/-- A failed `Unmarshal` returns `badRec`. -/
theorem goFail_badRec {C : WalCodec} {fs : List (List w8)} {off : Nat} {c : w32} {s : WalStop}
    {fs' : List (List w8)} {off' : Nat} {c' : w32} (h : GoFail C fs off c s fs' off' c') :
    ∃ t, s = .badRec t := by
  induction h with
  | here h => obtain ⟨_, _, _, _, rfl⟩ := h; exact ⟨_, rfl⟩
  | next _ _ ih => exact ih

/-- The frame `decRecStep` reads is `decFrame`'s. -/
theorem decRecStep_decFrame {C : WalCodec} {last : Bool} {bs : List w8} {off : Nat} {c : w32}
    {data : List w8} {rb : Nat} (h : decFrame bs off = some (data, rb)) :
    ∃ pad, decRecStep C last bs off c =
      match C.decRec (data.take rb) with
      | none => .stop (.badRec (isTorn last off data)) c
      | some r =>
        if r.typ ≠ crcType then
          if r.crc = C.crc32c c r.data then .accept r (8 + rb + pad) (C.crc32c c r.data)
          else .stop (.crcErr (isTorn last off data)) (C.crc32c c r.data)
        else .accept r (8 + rb + pad) c := by
  unfold decFrame at h
  unfold decRecStep
  simp only at h ⊢
  split at h; · cases h
  rename_i h1; rw [ite_eq_right h1]
  split at h; · cases h
  rename_i h2; rw [ite_eq_right h2]
  split at h; · cases h
  rename_i h3; rw [ite_eq_right h3]
  split at h; · cases h
  rename_i h4; rw [ite_eq_right h4]
  split at h; · cases h
  rename_i h5; rw [ite_eq_right h5]
  injection h with h; injection h with hd hr
  subst hd hr
  exact ⟨_, rfl⟩

/-! ## The reader's loop, run to its end -/

/-- **The readers' loop over `Decode`** (`for err = decoder.Decode(rec); err == nil; ...`, with
the CRC record's check and `UpdateCRC`, wal.go:523-593), as a relation: from the decoder state
`(fs, off, c)` the loop reads the records `rs` and stops with `s` (the error `Decode` returned, or
`.crcRec`), the decoder's state then `(fs', off', c')`. -/
inductive ReaderRun (C : WalCodec) :
    List (List w8) → Nat → w32 → List WalRec → WalStop → List (List w8) → Nat → w32 → Prop where
  | stop {fs off c s fs' off' c'} : goDecode C fs off c = .stop s fs' off' c' →
      ReaderRun C fs off c [] s fs' off' c'
  | crcRec {fs off c r fs' off' c'} : goDecode C fs off c = .ok r fs' off' c' →
      r.typ = crcType → crcRecBad c' r → ReaderRun C fs off c [] .crcRec fs' off' c'
  | fail {fs off c s fs' off' c'} : GoFail C fs off c s fs' off' c' →
      ReaderRun C fs off c [] s fs' off' c'
  | ok {fs off c r fs1 off1 c1 rs s fs' off' c'} : goDecode C fs off c = .ok r fs1 off1 c1 →
      ¬ (r.typ = crcType ∧ crcRecBad c1 r) →
      ReaderRun C fs1 off1 (rdCrc c1 r) rs s fs' off' c' →
      ReaderRun C fs off c (r :: rs) s fs' off' c'

/-- **The loop lemma**: the readers' loop from the decoder state `(fs, off, c)` reads what
`rdRest` says; from a fresh decoder, `walDecodeFiles` (`readerRun_start`). The offset and CRC
agree at every stop but a CRC mismatch (`LastOffset()`/`LastCRC()`, which the readers use only after
`io.EOF`). Or a `proto.Unmarshal` failed (`GoFail`): then the loop read the records `rdRest` reads
up to the decoder state `(fs1, off1, c1)` where it failed. -/
theorem readerRun_eq {C : WalCodec} {fs : List (List w8)} {off : Nat} {c : w32} {rs : List WalRec}
    {s : WalStop} {fs' : List (List w8)} {off' : Nat} {c' : w32}
    (h : ReaderRun C fs off c rs s fs' off' c') :
    ((rdRest C fs off c).recs = rs ∧ (rdRest C fs off c).stop = s ∧
      (s ≠ .crcRec → (∀ t, s ≠ .crcErr t) →
        (rdRest C fs off c).off = off' ∧ (rdRest C fs off c).crc = c')) ∨
    (∃ fs1 off1 c1, (rdRest C fs off c).recs = rs ++ (rdRest C fs1 off1 c1).recs ∧
      GoFail C fs1 off1 c1 s fs' off' c') := by
  induction h with
  | stop hd =>
    obtain ⟨h1, h2, h3⟩ := rdRest_stop hd
    exact Or.inl ⟨h1, h2, fun _ ht => h3 ht⟩
  | crcRec hd ht hb =>
    obtain ⟨h1, h2⟩ := rdRest_crcRec hd ⟨ht, hb⟩
    exact Or.inl ⟨h1, h2, fun h _ => absurd rfl h⟩
  | fail hf => exact Or.inr ⟨_, _, _, rfl, hf⟩
  | ok hd hok _ ih =>
    rw [rdRest_ok hd hok]
    rcases ih with ih | ⟨fs1, off1, c1, h1, h2⟩
    · exact Or.inl ⟨by rw [ih.1], ih.2.1, ih.2.2⟩
    · exact Or.inr ⟨fs1, off1, c1, by simp only [h1, List.cons_append], h2⟩

/-- The loop lemma from a fresh decoder (`NewDecoder(rs...)`: offset 0, CRC `crc.New(0, …)`). -/
theorem readerRun_start {C : WalCodec} {fs : List (List w8)} {rs : List WalRec} {s : WalStop}
    {fs' : List (List w8)} {off' : Nat} {c' : w32} (h : ReaderRun C fs 0 0#32 rs s fs' off' c') :
    ((walDecodeFiles C fs 0#32).recs = rs ∧ (walDecodeFiles C fs 0#32).stop = s ∧
      (s = .eof → (walDecodeFiles C fs 0#32).off = off' ∧ (walDecodeFiles C fs 0#32).crc = c')) ∨
    (∃ fs1 off1 c1, (walDecodeFiles C fs 0#32).recs = rs ++ (rdRest C fs1 off1 c1).recs ∧
      GoFail C fs1 off1 c1 s fs' off' c') := by
  rw [← rdRest_start]
  rcases readerRun_eq h with ⟨h1, h2, h3⟩ | h
  · exact Or.inl ⟨h1, h2, fun he => h3 (by subst he; decide) (by subst he; intro t h; cases h)⟩
  · exact Or.inr h

end WalEnc
end EtcdGrove
end Perennial
