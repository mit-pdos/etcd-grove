/- Lean-first (no Rocq counterpart).

# What `Repair`'s reader reads from the last segment (pure; law L2 of `wal.Repair`, W7 of `notes/wal-fsext-plan.md`)

`Repair` (S/repair.go:30-106) reads the WAL's last segment alone, with a fresh decoder (offset 0, CRC 0),
in the readers' loop (`Decode`, then on a CRC record `LastCRC`, `Validate` against a nonzero CRC and
`UpdateCRC`: `ReaderRun`'s steps), and on `io.ErrUnexpectedEOF` truncates the segment at `LastOffset()`,
the offset of the frame the failing `Decode` started at. The truncation removes no record of the
history when every stop is at the end of the segment's frames: law L2.

* `RepairFile C bs rs`: the file `bs` starts with the frames of `rs`, a CRC chain from 0, and the
  reader accepts nothing at their end at the chain's CRC.
* `RepairAt C rs off c`: the loop invariant, the decoder at the end of a prefix of `rs` at the chain's
  CRC after it.
* `repairAt_ok`, `repairAt_stop`, `repairAt_fail`: a record step keeps the invariant (the file not
  dropped); a stop (`goDecode`'s `.stop`) and a failed `proto.Unmarshal` (`GoFail`) happen only at the
  end of the frames.
* `walRepairFile`: the last segment of a WAL with no resize window on its tail and its stream all
  written (`TailIdle`'s `TailExact` and `wr = |stream|`) is a `RepairFile` whose frames end at `wr`.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadAllFiles
public import Proof.go_etcd_io.etcd.server.v3.storage.WalEncDecoder

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Fs WalEnc go_etcd_io.raft.v3

set_option autoImplicit false

section repair
variable [GooseExts]

/-- **What `Repair`'s reader reads** (see the file header). -/
structure RepairFile (C : WalCodec) (bs : List w8) (rs : List WalRec) : Prop where
  fit : RecsFit C rs
  chain : ChainOk C 0#32 rs
  pre : recFrames C rs <+: bs
  stop : ∀ r len c', decStep C true bs (recFrames C rs).length (chainEnd C 0#32 rs) ≠ .accept r len c'

/-- **The loop invariant** (see the file header). -/
def RepairAt (C : WalCodec) (rs : List WalRec) (off : Nat) (c : w32) : Prop :=
  ∃ xs ys, rs = xs ++ ys ∧ off = (recFrames C xs).length ∧ c = chainEnd C 0#32 xs

theorem repairAt_start (C : WalCodec) (rs : List WalRec) : RepairAt C rs 0 0#32 :=
  ⟨[], rs, rfl, rfl, rfl⟩

/-- `goDecode` on one file. -/
theorem goDecode_one (C : WalCodec) (bs : List w8) (off : Nat) (c : w32) :
    goDecode C [bs] off c =
      match decRecStep C true bs off c with
      | .eof => .stop .eof [] off c
      | .stop s c' => .stop s [bs] off c'
      | .accept r len c' => .ok r [bs] (off + len) c' := by
  simp only [goDecode, List.isEmpty_nil]
  cases decRecStep C true bs off c <;> rfl

/-- The file past the frames of a prefix `xs` of `rs`: the frames of the rest, then more. -/
theorem repairFile_drop {C : WalCodec} {bs : List w8} {rs xs ys : List WalRec}
    (hf : RepairFile C bs rs) (hrs : rs = xs ++ ys) :
    ∃ t, bs.drop (recFrames C xs).length = recFrames C ys ++ t := by
  obtain ⟨t, ht⟩ := hf.pre
  refine ⟨t, ?_⟩
  rw [← ht, hrs, recFrames_append, List.append_assoc]
  exact List.drop_left' rfl

/-- The reader's step accepting the decoder's record (not a CRC record it rejects). -/
theorem decStep_of_recStep {C : WalCodec} {bs : List w8} {off : Nat} {c c1 : w32} {r : WalRec}
    {len : Nat} (hs : decRecStep C true bs off c = .accept r len c1)
    (hok : ¬ (r.typ = crcType ∧ crcRecBad c1 r)) :
    decStep C true bs off c = .accept r len (rdCrc c1 r) := by
  rw [decStep_eq, hs]
  by_cases ht : r.typ = crcType
  · have hc := decRecStep_crc hs ht
    subst hc
    simp only [ht, ite_true, rdCrc]
    rw [ite_eq_right (fun hb => absurd hb (fun hb => hok ⟨ht, hb⟩))]
  · simp only [ht, ite_false, rdCrc]

/-- At a prefix whose rest is not empty, the reader accepts the next record. -/
theorem repairAt_next {C : WalCodec} (hC : C.Ok) {bs : List w8} {rs xs : List WalRec} {y : WalRec}
    {ys : List WalRec} (hf : RepairFile C bs rs) (hrs : rs = xs ++ y :: ys) :
    decStep C true bs (recFrames C xs).length (chainEnd C 0#32 xs) =
      .accept y (frame (C.encRec y)).length (crcNext C (chainEnd C 0#32 xs) y) := by
  obtain ⟨t, ht⟩ := repairFile_drop hf hrs
  rw [recFrames_cons, List.append_assoc] at ht
  have hch := hf.chain
  rw [hrs, chainOk_append] at hch
  exact decStep_frame hC true (hf.fit y (by rw [hrs]; simp)) ht hch.2.1

/-- **A record step keeps the invariant** (the file not dropped). -/
theorem repairAt_ok {C : WalCodec} (hC : C.Ok) {bs : List w8} {rs : List WalRec} {off off1 : Nat}
    {c c1 : w32} {r : WalRec} {fs1 : List (List w8)} (hf : RepairFile C bs rs)
    (ha : RepairAt C rs off c) (h : goDecode C [bs] off c = .ok r fs1 off1 c1)
    (hok : ¬ (r.typ = crcType ∧ crcRecBad c1 r)) :
    fs1 = [bs] ∧ RepairAt C rs off1 (rdCrc c1 r) := by
  rw [goDecode_one] at h
  split at h
  · cases h
  · cases h
  · rename_i r0 len c0 hs
    injection h with h1 h2 h3 h4
    subst r0 fs1 off1 c0
    have hdec := decStep_of_recStep hs hok
    obtain ⟨xs, ys, hrs, hoff, hc⟩ := ha
    subst hoff hc
    cases ys with
    | nil =>
      rw [List.append_nil] at hrs; subst hrs
      exact absurd hdec (hf.stop _ _ _)
    | cons y ys =>
      rw [repairAt_next hC hf hrs] at hdec
      injection hdec with e1 e2 e3
      subst e1 e2
      refine ⟨rfl, xs ++ [y], ys, by rw [hrs]; simp, ?_, ?_⟩
      · rw [recFrames_append, List.length_append, recFrames_cons, recFrames_nil, List.append_nil]
      · rw [← e3, chainEnd_append]; rfl

/-- **A stop happens only at the end of the frames.** -/
theorem repairAt_stop {C : WalCodec} (hC : C.Ok) {bs : List w8} {rs : List WalRec} {off off' : Nat}
    {c c' : w32} {s : WalStop} {fs' : List (List w8)} (hf : RepairFile C bs rs)
    (ha : RepairAt C rs off c) (h : goDecode C [bs] off c = .stop s fs' off' c') :
    off = (recFrames C rs).length := by
  obtain ⟨xs, ys, hrs, hoff, hc⟩ := ha
  subst hoff hc
  cases ys with
  | nil => rw [hrs, List.append_nil]
  | cons y ys =>
    have hdec := repairAt_next hC hf hrs
    rw [goDecode_one] at h
    rw [decStep_eq] at hdec
    split at h
    · rename_i hs; rw [hs] at hdec; cases hdec
    · rename_i s0 c0 hs; rw [hs] at hdec; cases hdec
    · cases h

/-- The frame `decodeRecord` hands to `proto.Unmarshal` at a frame the encoder wrote is the record's
encoding (with its padding). -/
theorem decFrame_ofFrame {C : WalCodec} (hC : C.Ok) {bs : List w8} {off : Nat} {r : WalRec}
    {rest : List w8} (hfit : (C.encRec r).length < 2 ^ 56)
    (hbs : bs.drop off = frame (C.encRec r) ++ rest) :
    ∃ data, decFrame bs off = some (data, (C.encRec r).length) ∧
      data.take (C.encRec r).length = C.encRec r := by
  have hn0 : (C.encRec r).length ≠ 0 := by
    intro h; exact hC.enc_ne r (List.length_eq_zero_iff.mp h)
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
  have hfs := decodeFrameSize_encode _ hfit
  have hne := encodeFrameSize_ne_zero _ hfit hn0
  refine ⟨C.encRec r ++ List.replicate (framePad (C.encRec r).length) (0#8), ?_, List.take_left' rfl⟩
  unfold decFrame
  simp only [htake, u64Le_to_word, hfs, hdata]
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right hne, ite_eq_right (by omega),
    ite_eq_right (by omega)]

/-- **A failed `proto.Unmarshal` happens only at the end of the frames** (the frames before it are
the encoder's, which `Unmarshal` decodes). -/
theorem repairAt_fail {C : WalCodec} (hC : C.Ok) {bs : List w8} {rs : List WalRec} {off off' : Nat}
    {c c' : w32} {s : WalStop} {fs' : List (List w8)} (hf : RepairFile C bs rs)
    (ha : RepairAt C rs off c) (h : GoFail C [bs] off c s fs' off' c') :
    off = (recFrames C rs).length := by
  obtain ⟨xs, ys, hrs, hoff, hc⟩ := ha
  subst hoff hc
  cases ys with
  | nil => rw [hrs, List.append_nil]
  | cons y ys =>
    cases h with
    | here hfail =>
      obtain ⟨data, rb, hd, hu, -⟩ := hfail
      obtain ⟨t, ht⟩ := repairFile_drop hf hrs
      rw [recFrames_cons, List.append_assoc] at ht
      obtain ⟨data', hd', htk⟩ := decFrame_ofFrame hC (hf.fit y (by rw [hrs]; simp)) ht
      rw [hd'] at hd
      injection hd with hd; injection hd with e1 e2
      subst e1 e2
      exact absurd htk (hu y)

/-! ## The last segment of an idle WAL -/

/-- A chain from any CRC whose first record is a CRC record is a chain from 0, with the same end. -/
theorem chainOk_crcHead {C : WalCodec} {c : w32} {r : WalRec} {rs : List WalRec}
    (h : ChainOk C c (r :: rs)) (ht : r.typ = crcType) :
    ChainOk C 0#32 (r :: rs) ∧ chainEnd C 0#32 (r :: rs) = chainEnd C c (r :: rs) := by
  have e : crcNext C 0#32 r = crcNext C c r := by simp [crcNext, ht]
  refine ⟨⟨by simp [CrcOk, ht], ?_⟩, ?_⟩
  · rw [e]; exact h.2
  · simp only [chainEnd, e]

/-- The last segment's records start with a CRC record. -/
theorem lastRecs_head (C : WalCodec) (M : WalMarshal) (md : List w8) (A : List WalHist) (Sl : WalHist) :
    ∃ r rs, lastRecs C M md A Sl = r :: rs ∧ r.typ = crcType := by
  unfold lastRecs segHdrDs
  split <;> simp [hdrDs, cutHdrDs, chainRecs]

/-- **The last segment of a WAL with no resize window on its tail and its stream all written is a
`RepairFile`**, its frames ending at `wr` (see the file header). -/
theorem walRepairFile {C : WalCodec} (hC : C.Ok) {Mr : WalMarshal} {d : WalDur} {lay : WalLay}
    {ents : Ents} (hab : WalAbsD C Mr d lay ents) (hex : TailExact lay)
    (hwr : lay.wr = (segStream C Mr d lay.cuts lay.cuts.length).length) (gL : SegG)
    (hgL' : lay.segs.getLast? = some gL) :
    ∃ rs, RepairFile C (segImg gL) rs ∧ (recFrames C rs).length = lay.wr := by
  -- The history's segments.
  generalize hSs : segsOf (histM d) lay.cuts = Ss
  have hSsl : Ss.length = lay.cuts.length + 1 := by rw [← hSs]; simp [segsOf]
  have hSne : Ss ≠ [] := by intro h; rw [h] at hSsl; simp at hSsl
  have hsplit : Ss = Ss.dropLast ++ [Ss.getLast hSne] := (List.dropLast_concat_getLast _).symm
  generalize hA : Ss.dropLast = A at hsplit
  generalize hSl : Ss.getLast hSne = Sl at hsplit
  have hAl : A.length = lay.cuts.length := by rw [← hA, List.length_dropLast, hSsl]; simp
  have hrecs : segRecs C Mr d lay.cuts =
      chainSegs C 0#32 (segsDs Mr d.metadata true [] A) ++ [lastRecs C Mr d.metadata A Sl] := by
    unfold segRecs; rw [hSs, hsplit, chainSegs_snocR]
  have hlenA : (chainSegs C 0#32 (segsDs Mr d.metadata true [] A)).length = A.length := by
    rw [length_chainSegs, length_segsDs]
  have hstreamL : segStream C Mr d lay.cuts lay.cuts.length =
      recFrames C (lastRecs C Mr d.metadata A Sl) := by
    unfold segStream; rw [hrecs, ← hAl, ← hlenA, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by omega)]
    simp
  have hTL := hab.lastEx hex gL hgL'
  have himg := tailLast_img hTL hwr
  -- The records: their fit and chain.
  have hrecsAll : recsOfSegs C Mr d.metadata Ss =
      recsOfSegs C Mr d.metadata A ++ lastRecs C Mr d.metadata A Sl := by
    rw [hsplit, recsOfSegs_snocR]
  have hfit : RecsFit C (lastRecs C Mr d.metadata A Sl) := by
    intro r hr; apply hab.fit; rw [hSs, hrecsAll]; exact List.mem_append_right _ hr
  have hds : ∀ p ∈ segHdrDs Mr d.metadata (if A = [] then true else false) A.flatten ++
      Sl.flatMap (opDs Mr), p.1 = crcType → p.2 = [] := by
    intro p hp
    apply segsDs_crcOk Mr d.metadata true [] (A ++ [Sl])
    rw [segsDs_append, List.flatten_append]
    apply List.mem_append_right
    simp only [segsDs, List.flatten_cons, List.flatten_nil, List.append_nil, List.nil_append]
    exact hp
  have hch0 : ChainOk C (crcAfter C 0#32 (segsDs Mr d.metadata true [] A).flatten)
      (lastRecs C Mr d.metadata A Sl) := chainOk_chainRecs hC _ _ hds
  obtain ⟨r0, rs0, hrs0, ht0⟩ := lastRecs_head C Mr d.metadata A Sl
  rw [hrs0] at hch0
  obtain ⟨hch, hend⟩ := chainOk_crcHead hch0 ht0
  rw [← hrs0] at hch hend
  refine ⟨lastRecs C Mr d.metadata A Sl, ⟨hfit, hch, ?_, ?_⟩, by rw [hwr, hstreamL]⟩
  · rw [himg, ← hstreamL]; exact List.prefix_append _ _
  · intro r len c'
    rw [hend, chainEnd_lastRecs, ← hstreamL, ← hsplit, ← hSs]
    obtain ⟨-, -, h3, h4, -, h6, h7, h8⟩ := hTL
    generalize hS : segStream C Mr d lay.cuts lay.cuts.length = S at *
    by_cases hz : lay.z0 < S.length
    · apply decStep_zeros_any C true (z := lay.old.length - S.length)
      rw [himg, List.drop_left]
      apply List.ext_getElem
      · simp
      · intro b hb1 hb2
        simp only [List.getElem_drop, List.getElem_replicate]
        have := h8 hz (S.length + b) (by omega) (by simp at hb1; omega)
        rwa [getD_of_lt _ _ _ (by simp at hb1; omega)] at this
    · have hz0 : lay.z0 = S.length := by omega
      have hold : segImg gL = lay.old := by
        rw [himg]
        have : S = lay.old.take S.length := by rw [← hz0, ← h7, hz0, List.take_length]
        conv => lhs; arg 1; rw [this]
        exact List.take_append_drop _ _
      rw [hold, ← hz0]
      exact hab.tailStop (by rw [hS]; exact hz0) r len c'

end repair

end WalFs
end EtcdGrove
end Perennial

end
