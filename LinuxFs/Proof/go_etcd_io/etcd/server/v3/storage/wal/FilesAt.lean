/- Lean-first (no Rocq counterpart).

# The decoder at a frame boundary of the encoder's frames, across files (pure; gap 4 of W8, `notes/wal-fsext-plan.md`)

`validSnapshotEntries` (S/wal.go:723-791) and `ReadAll` in read mode take `io.ErrUnexpectedEOF` for the end
of the WAL, and a torn record whose `proto.Unmarshal` failed returns it (`GoFail`, `WalStop.badRec true`).
`proto.Unmarshal` may fail on bytes that are no record's encoding where the pure reader (`rdRest`, over the
canonical decoding `C.decRec`) would go on, so a failed `Unmarshal` before the stream's end would end the
read early. It does not happen on a WAL's files: every frame before the end is the encoder's, whose bytes
are a record's encoding (`decFrame_ofFrame`), and past the end the reader accepts nothing.

* `FilesOk C c rss R last`: full files holding exactly the frames of `rss`, then a last file whose frames
  of `R` are a prefix, the records one CRC chain from `c`, and the reader accepting nothing at their end
  (`walDecodeFiles_running`'s premises, per file).
* `FilesAt C fs off c`: the decoder `(fs, off, c)` at the end of a prefix `xs` of the current file's
  records, `c` the chain's value after it, and the rest `FilesOk`.
* `filesAt_start`: a fresh decoder (offset 0) on `FilesOk` files; `filesAt_ok`: a record step keeps it
  (`goDecode`'s `.ok`, the reader's CRC check passed: `vsLoop_ok`'s step); `filesAt_fail`: at a failed
  `Unmarshal`, the reader reads no record from the decoder's state (`(rdRest C fs off c).recs = []`).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.RepairDecode

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Fs WalEnc

set_option autoImplicit false

section filesAt
variable [GooseExts]

/-- **Full files, then a last file** (see the file header). -/
def FilesOk (C : WalCodec) (c : w32) (rss : List (List WalRec)) (R : List WalRec) (last : List w8) : Prop :=
  RecsFit C (rss.flatten ++ R) ∧ ChainOk C c (rss.flatten ++ R) ∧ recFrames C R <+: last ∧
  ∀ r len c', decStep C true last (recFrames C R).length (chainEnd C c (rss.flatten ++ R)) ≠ .accept r len c'

/-- **The decoder at a frame boundary** (see the file header). -/
def FilesAt (C : WalCodec) (fs : List (List w8)) (off : Nat) (c : w32) : Prop :=
  ∃ (c0 : w32) (xs ys : List WalRec) (rss : List (List WalRec)) (R : List WalRec) (last : List w8),
    off = (recFrames C xs).length ∧ c = chainEnd C c0 xs ∧
    ((fs = recFrames C (xs ++ ys) :: (rss.map (recFrames C) ++ [last]) ∧
        RecsFit C (xs ++ ys) ∧ ChainOk C c0 (xs ++ ys) ∧ FilesOk C (chainEnd C c0 (xs ++ ys)) rss R last) ∨
      (fs = [last] ∧ FilesOk C c0 [] (xs ++ ys) last))

/-- **A fresh decoder** on `FilesOk` files. -/
theorem filesAt_start {C : WalCodec} {c0 : w32} {rss : List (List WalRec)} {R : List WalRec}
    {last : List w8} (h : FilesOk C c0 rss R last) :
    FilesAt C (rss.map (recFrames C) ++ [last]) 0 c0 := by
  obtain ⟨hfit, hch, hpre, hend⟩ := h
  cases rss with
  | nil =>
    refine ⟨c0, [], R, [], [], last, rfl, rfl, Or.inr ⟨rfl, ?_⟩⟩
    exact ⟨hfit, hch, hpre, hend⟩
  | cons rs rss =>
    have hfl : (rs :: rss).flatten ++ R = rs ++ (rss.flatten ++ R) := by simp
    rw [hfl] at hfit hch hend
    rw [chainOk_append] at hch
    refine ⟨c0, [], rs, rss, R, last, rfl, rfl, Or.inl ⟨rfl, ?_, hch.1, ?_⟩⟩
    · exact fun r hr => hfit r (List.mem_append_left _ hr)
    · refine ⟨fun r hr => hfit r (List.mem_append_right _ hr), hch.2, hpre, ?_⟩
      intro r len c'
      rw [← chainEnd_append]
      exact hend r len c'

/-- The reader's step from the decoder's (`decStep_of_recStep` for any `last`). -/
theorem decStep_of_recStep' {C : WalCodec} {last : Bool} {bs : List w8} {off : Nat} {c c1 : w32}
    {r : WalRec} {len : Nat} (hs : decRecStep C last bs off c = .accept r len c1)
    (hok : ¬ (r.typ = crcType ∧ crcRecBad c1 r)) :
    decStep C last bs off c = .accept r len (rdCrc c1 r) := by
  rw [decStep_eq, hs]
  by_cases ht : r.typ = crcType
  · have hc := decRecStep_crc hs ht
    subst hc
    simp only [ht, ite_true, rdCrc]
    rw [ite_eq_right (fun hb => absurd hb (fun hb => hok ⟨ht, hb⟩))]
  · simp only [ht, ite_false, rdCrc]

/-- At the end of a file, the decoder's step is `.eof`. -/
theorem decRecStep_fileEnd (C : WalCodec) (last : Bool) (bs : List w8) (c : w32) :
    decRecStep C last bs bs.length c = .eof := by
  unfold decRecStep
  simp

/-- At the end of a file, there is no frame. -/
theorem decFrame_end (bs : List w8) : decFrame bs bs.length = none := by
  unfold decFrame
  simp

/-- The frames of `xs ++ y :: ys` past those of `xs`. -/
theorem frames_drop_cons (C : WalCodec) (xs ys : List WalRec) (y : WalRec) (t : List w8) :
    (recFrames C (xs ++ y :: ys) ++ t).drop (recFrames C xs).length =
      frame (C.encRec y) ++ (recFrames C ys ++ t) := by
  rw [recFrames_append, recFrames_cons, List.append_assoc, List.drop_left', List.append_assoc]
  rfl

/-- **The step at a record's frame**: the decoder accepts it, the reader too, at the chain's next value. -/
theorem recStep_frame {C : WalCodec} (hC : C.Ok) (last : Bool) {bs : List w8} {off : Nat} {c : w32}
    {y : WalRec} {rest : List w8} (hfit : (C.encRec y).length < 2 ^ 56)
    (hbs : bs.drop off = frame (C.encRec y) ++ rest) (hcrc : CrcOk C c y) {r : WalRec} {len : Nat}
    {c1 : w32} (hs : decRecStep C last bs off c = .accept r len c1)
    (hok : ¬ (r.typ = crcType ∧ crcRecBad c1 r)) :
    r = y ∧ len = (frame (C.encRec y)).length ∧ rdCrc c1 r = crcNext C c y := by
  have h1 := decStep_of_recStep' hs hok
  rw [decStep_frame hC last hfit hbs hcrc] at h1
  injection h1 with e1 e2 e3
  exact ⟨e1.symm, e2.symm, e3.symm⟩

/-- At a record's frame, the decoder's step is no `.eof`. -/
theorem recStep_frame_ne_eof {C : WalCodec} (hC : C.Ok) (last : Bool) {bs : List w8} {off : Nat}
    {c : w32} {y : WalRec} {rest : List w8} (hfit : (C.encRec y).length < 2 ^ 56)
    (hbs : bs.drop off = frame (C.encRec y) ++ rest) (hcrc : CrcOk C c y) :
    decRecStep C last bs off c ≠ .eof := by
  intro h
  have h1 := decStep_frame hC last hfit hbs hcrc
  rw [decStep_eq, h] at h1
  cases h1

/-- At a record's frame, `proto.Unmarshal` does not fail. -/
theorem recFail_frame {C : WalCodec} (hC : C.Ok) (last : Bool) {bs : List w8} {off : Nat}
    {y : WalRec} {rest : List w8} (hfit : (C.encRec y).length < 2 ^ 56)
    (hbs : bs.drop off = frame (C.encRec y) ++ rest) {s : WalStop} :
    ¬ RecFail C last bs off s := by
  rintro ⟨data, rb, hd, hu, -⟩
  obtain ⟨data', hd', htk⟩ := decFrame_ofFrame hC hfit hbs
  rw [hd'] at hd
  injection hd with hd; injection hd with e1 e2
  subst e1 e2
  exact hu y htk

/-- The current file's records split at the decoder: the next frame, or the end. -/
theorem filesAt_cur {C : WalCodec} {c0 : w32} {xs ys : List WalRec} (hfit : RecsFit C (xs ++ ys))
    (hch : ChainOk C c0 (xs ++ ys)) :
    ys = [] ∨ ∃ y ys', ys = y :: ys' ∧ (C.encRec y).length < 2 ^ 56 ∧ CrcOk C (chainEnd C c0 xs) y ∧
      RecsFit C (xs ++ [y] ++ ys') ∧ ChainOk C c0 (xs ++ [y] ++ ys') := by
  cases ys with
  | nil => exact .inl rfl
  | cons y ys' =>
    refine .inr ⟨y, ys', rfl, hfit y (by simp), ?_, by simpa using hfit, by simpa using hch⟩
    rw [chainOk_append] at hch
    exact hch.2.1

/-- **A record step keeps the boundary** (see the file header). -/
theorem filesAt_ok {C : WalCodec} (hC : C.Ok) :
    ∀ {fs : List (List w8)} {off : Nat} {c : w32} {r : WalRec} {fs' : List (List w8)} {off' : Nat}
      {c' : w32}, FilesAt C fs off c → goDecode C fs off c = .ok r fs' off' c' →
      ¬ (r.typ = crcType ∧ crcRecBad c' r) → FilesAt C fs' off' (rdCrc c' r) := by
  intro fs
  induction fs with
  | nil =>
    intro off c r fs' off' c' hA
    obtain ⟨_, _, _, _, _, _, _, _, ⟨h, _⟩ | ⟨h, _⟩⟩ := hA <;> cases h
  | cons f rest ih =>
    intro off c r fs' off' c' hA h hok
    obtain ⟨c0, xs, ys, rss, R, last, hoff, hc, hcase⟩ := hA
    rcases hcase with ⟨hfs, hfit, hch, hok'⟩ | ⟨hfs, hfo⟩
    · -- a full file
      injection hfs with hf hrest
      subst hf hrest
      obtain ⟨g, gs, hgs⟩ : ∃ g gs, rss.map (recFrames C) ++ [last] = g :: gs := by
        cases hh : rss.map (recFrames C) ++ [last] with
        | nil => simp at hh
        | cons g gs => exact ⟨g, gs, rfl⟩
      have hA' := filesAt_start hok'
      rw [hgs] at hA' ih h
      rcases filesAt_cur hfit hch with rfl | ⟨y, ys', rfl, hfy, hcy, hfit', hch'⟩
      · -- the file's end: the next file from 0
        simp only [List.append_nil] at hfit hch hok' h hA'
        have he : decRecStep C false (recFrames C xs) off c = .eof := by
          rw [hoff]; exact decRecStep_fileEnd C false _ c
        simp only [goDecode, List.isEmpty_cons, he] at h
        rw [← hc] at hA'
        exact ih hA' h hok
      · -- a record
        have hbs : (recFrames C (xs ++ y :: ys')).drop off = frame (C.encRec y) ++ (recFrames C ys' ++ []) := by
          rw [hoff, ← frames_drop_cons C xs ys' y [], List.append_nil]
        simp only [goDecode, List.isEmpty_cons] at h
        generalize hd : decRecStep C false (recFrames C (xs ++ y :: ys')) off c = st at h
        cases st with
        | eof => exact absurd hd (recStep_frame_ne_eof hC false hfy hbs (hc ▸ hcy))
        | stop s c2 => cases h
        | accept r0 len c1 =>
          injection h with e1 e2 e3 e4
          subst e1 e2 e3 e4
          obtain ⟨rfl, rfl, hcr⟩ := recStep_frame hC false hfy hbs (hc ▸ hcy) hd hok
          refine ⟨c0, xs ++ [r0], ys', rss, R, last, ?_, ?_, Or.inl ⟨?_, hfit', hch', ?_⟩⟩
          · rw [hoff, recFrames_append, List.length_append, recFrames_cons, recFrames_nil,
              List.append_nil]
          · rw [hcr, hc, chainEnd_append]; rfl
          · rw [hgs]; simp
          · simpa using hok'
    · -- the last file
      injection hfs with hf hrest
      subst hrest
      have hf' := hf.symm
      subst hf'
      obtain ⟨hfit, hch, hpre, hend⟩ := hfo
      simp only [List.flatten_nil, List.nil_append] at hfit hch hend
      rw [goDecode_one] at h
      generalize hd : decRecStep C true last off c = st at h
      cases st with
      | eof => cases h
      | stop s c2 => cases h
      | accept r0 len c1 =>
        injection h with e1 e2 e3 e4
        subst e1 e2 e3 e4
        rcases filesAt_cur hfit hch with rfl | ⟨y, ys', rfl, hfy, hcy, hfit', hch'⟩
        · rw [List.append_nil] at hend
          have h1 := decStep_of_recStep' hd hok
          rw [hoff, hc] at h1
          exact absurd h1 (hend _ _ _)
        · obtain ⟨t, ht⟩ := hpre
          have hbs : last.drop off = frame (C.encRec y) ++ (recFrames C ys' ++ t) := by
            rw [hoff, ← ht]; exact frames_drop_cons C xs ys' y t
          obtain ⟨rfl, rfl, hcr⟩ := recStep_frame hC true hfy hbs (hc ▸ hcy) hd hok
          refine ⟨c0, xs ++ [r0], ys', [], [], last, ?_, ?_, Or.inr ⟨rfl, ?_⟩⟩
          · rw [hoff, recFrames_append, List.length_append, recFrames_cons, recFrames_nil,
              List.append_nil]
          · rw [hcr, hc, chainEnd_append]; rfl
          · refine ⟨by simpa using hfit', by simpa using hch', ⟨t, ?_⟩, ?_⟩
            · rw [← ht]; simp
            · simpa using hend

/-- **At a failed `Unmarshal` the reader reads no record** (see the file header). -/
theorem filesAt_fail {C : WalCodec} (hC : C.Ok) :
    ∀ {fs : List (List w8)} {off : Nat} {c : w32} {s : WalStop} {fs' : List (List w8)} {off' : Nat}
      {c' : w32}, FilesAt C fs off c → GoFail C fs off c s fs' off' c' → (rdRest C fs off c).recs = [] := by
  intro fs
  induction fs with
  | nil =>
    intro off c s fs' off' c' hA
    obtain ⟨_, _, _, _, _, _, _, _, ⟨h, _⟩ | ⟨h, _⟩⟩ := hA <;> cases h
  | cons f rest ih =>
    intro off c s fs' off' c' hA h
    obtain ⟨c0, xs, ys, rss, R, last, hoff, hc, hcase⟩ := hA
    rcases hcase with ⟨hfs, hfit, hch, hok'⟩ | ⟨hfs, hfo⟩
    · -- a full file
      injection hfs with hf hrest
      subst hf hrest
      obtain ⟨g, gs, hgs⟩ : ∃ g gs, rss.map (recFrames C) ++ [last] = g :: gs := by
        cases hh : rss.map (recFrames C) ++ [last] with
        | nil => simp at hh
        | cons g gs => exact ⟨g, gs, rfl⟩
      have hA' := filesAt_start hok'
      rw [hgs] at hA' ih h ⊢
      rcases filesAt_cur hfit hch with rfl | ⟨y, ys', rfl, hfy, hcy, -, -⟩
      · simp only [List.append_nil] at hfit hch hok' hA' h ⊢
        have he : decRecStep C false (recFrames C xs) off c = .eof := by
          rw [hoff]; exact decRecStep_fileEnd C false _ c
        rw [rdRest_next (List.cons_ne_nil g gs) (by rw [List.isEmpty_cons]; exact he)]
        rw [← hc] at hA'
        cases h with
        | here hf =>
          obtain ⟨data, rb, hd, -, -⟩ := hf
          rw [hoff, decFrame_end] at hd
          cases hd
        | next _ hg => exact ih hA' hg
      · have hbs : (recFrames C (xs ++ y :: ys')).drop off = frame (C.encRec y) ++ (recFrames C ys' ++ []) := by
          rw [hoff, ← frames_drop_cons C xs ys' y [], List.append_nil]
        cases h with
        | here hf => exact absurd hf (recFail_frame hC _ hfy hbs)
        | next he _ => exact absurd he (recStep_frame_ne_eof hC false hfy hbs (hc ▸ hcy))
    · -- the last file
      injection hfs with hf hrest
      subst hrest
      have hf' := hf.symm
      subst hf'
      obtain ⟨hfit, hch, hpre, hend⟩ := hfo
      simp only [List.flatten_nil, List.nil_append] at hfit hch hend
      rcases filesAt_cur hfit hch with rfl | ⟨y, ys', rfl, hfy, hcy, -, -⟩
      · rw [List.append_nil] at hend
        show (walDecodeFrom C true last off c).recs = []
        rw [walDecodeFrom_unfold]
        generalize hd : decStep C true last off c = st
        cases st with
        | stop s0 => rfl
        | accept r len c1 =>
          rw [hoff, hc] at hd
          exact absurd hd (hend _ _ _)
      · obtain ⟨t, ht⟩ := hpre
        have hbs : last.drop off = frame (C.encRec y) ++ (recFrames C ys' ++ t) := by
          rw [hoff, ← ht]; exact frames_drop_cons C xs ys' y t
        cases h with
        | here hf => exact absurd hf (recFail_frame hC _ hfy hbs)

end filesAt

end WalFs
end EtcdGrove
end Perennial

end
