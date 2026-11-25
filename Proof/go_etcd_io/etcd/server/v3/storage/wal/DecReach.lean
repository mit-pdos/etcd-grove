/- Lean-first (no Rocq counterpart).

# Where the Go decoder is after `n` records (pure; P6 E3, the torn-`Save` fix)

`ReadAll` saves the decoder's position before the first of a run of entry records (`pendOff`,
`pendCRC`: `lastOff`/`lastCRC`, the decoder's `LastOffset()`/`LastCRC()` after the record before), and a
write-mode read seeks the tail there when the run is the last thing read (`notes/wal-p6-handoff.md`,
"Session 3", item 1). That position is the last segment's write position `wr`: not by reasoning back
from where the reader ended (two offsets can decode the same number of records to the same end; a
decoded frame's length need not be its record's encoding's), but forward. `Reach C fs off c fs' off' c' n`:
the reader's loop goes from the decoder state `(fs, off, c)` to `(fs', off', c')` in `n` accepted records
(`goDecode`, the reader's CRC-record check, `rdCrc`); it is deterministic (`reach_det`), and over the
files of a WAL it reaches the last file's write position after the WAL's records (`reach_files`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.WalEncDecoder

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalEnc

section reach


/-- **The reader's loop from `(fs, off, c)` to `(fs', off', c')` in `n` accepted records.** -/
inductive Reach (C : WalCodec) : List (List w8) → Nat → w32 → List (List w8) → Nat → w32 → Nat → Prop
  | refl (fs : List (List w8)) (off : Nat) (c : w32) : Reach C fs off c fs off c 0
  | step {fs : List (List w8)} {off : Nat} {c : w32} {r : WalRec} {fs1 : List (List w8)} {off1 : Nat}
      {c1 : w32} {gs : List (List w8)} {off2 : Nat} {c2 : w32} {n : Nat} :
      goDecode C fs off c = .ok r fs1 off1 c1 → ¬ (r.typ = crcType ∧ crcRecBad c1 r) →
      Reach C fs1 off1 (rdCrc c1 r) gs off2 c2 n → Reach C fs off c gs off2 c2 (n + 1)

/-- **The loop is deterministic**: the state after `n` records is unique. -/
theorem reach_det {C : WalCodec} {fs : List (List w8)} {off : Nat} {c : w32} {n : Nat}
    {g1 : List (List w8)} {o1 : Nat} {c1 : w32} {g2 : List (List w8)} {o2 : Nat} {c2 : w32}
    (h1 : Reach C fs off c g1 o1 c1 n) (h2 : Reach C fs off c g2 o2 c2 n) :
    g1 = g2 ∧ o1 = o2 ∧ c1 = c2 := by
  induction h1 with
  | refl => cases h2; exact ⟨rfl, rfl, rfl⟩
  | step hd _ _ ih =>
    cases h2 with
    | step hd' _ hr' =>
      rw [hd] at hd'
      injection hd' with e1 e2 e3 e4
      subst e1 e2 e3 e4
      exact ih hr'

/-- One more record at the end. -/
theorem reach_snoc {C : WalCodec} {fs : List (List w8)} {off : Nat} {c : w32} {n : Nat}
    {g : List (List w8)} {o : Nat} {c0 : w32} (h : Reach C fs off c g o c0 n)
    {r : WalRec} {g1 : List (List w8)} {o1 : Nat} {c1 : w32}
    (hd : goDecode C g o c0 = .ok r g1 o1 c1) (hok : ¬ (r.typ = crcType ∧ crcRecBad c1 r)) :
    Reach C fs off c g1 o1 (rdCrc c1 r) (n + 1) := by
  induction h with
  | refl => exact .step hd hok (.refl _ _ _)
  | step hd0 hok0 _ ih => exact .step hd0 hok0 (ih hd)

theorem reach_trans {C : WalCodec} {fs : List (List w8)} {off : Nat} {c : w32} {n m : Nat}
    {g : List (List w8)} {o : Nat} {c0 : w32} {g' : List (List w8)} {o' : Nat} {c' : w32}
    (h1 : Reach C fs off c g o c0 n) (h2 : Reach C g o c0 g' o' c' m) :
    Reach C fs off c g' o' c' (n + m) := by
  induction h1 with
  | refl => simpa using h2
  | step hd hok _ ih =>
    rw [Nat.add_right_comm]
    exact .step hd hok (ih h2)

/-- **A frame the encoder wrote, read by the Go decoder**: the record, the offset past its frame, and
the chain's next CRC (`rdCrc`), the reader's CRC check passing. -/
theorem goDecode_frame {C : WalCodec} (hC : C.Ok) {bs : List w8} {fs : List (List w8)} {off : Nat}
    {c : w32} {r : WalRec} {rest : List w8} (hfit : (C.encRec r).length < 2 ^ 56)
    (hbs : bs.drop off = frame (C.encRec r) ++ rest) (hcrc : CrcOk C c r) :
    ∃ c1, goDecode C (bs :: fs) off c = .ok r (bs :: fs) (off + (frame (C.encRec r)).length) c1 ∧
      ¬ (r.typ = crcType ∧ crcRecBad c1 r) ∧ rdCrc c1 r = crcNext C c r := by
  have hs := decStep_frame hC fs.isEmpty hfit hbs hcrc
  rw [decStep_eq] at hs
  unfold goDecode
  generalize hd : decRecStep C fs.isEmpty bs off c = d at hs
  cases d with
  | eof => cases hs
  | stop s c' => cases hs
  | accept r' len c' =>
    simp only at hs
    by_cases ht : r'.typ = crcType
    · have hc' := decRecStep_crc hd ht
      subst hc'
      rw [if_pos ht] at hs
      by_cases hb : crcRecBad c' r'
      · rw [if_pos hb] at hs; cases hs
      · rw [if_neg hb] at hs
        injection hs with e1 e2 e3
        subst e1 e2
        refine ⟨_, rfl, fun h => hb h.2, ?_⟩
        rw [← e3]; simp only [rdCrc, if_pos ht]
    · rw [if_neg ht] at hs
      injection hs with e1 e2 e3
      subst e1 e2 e3
      refine ⟨_, rfl, fun h => ht h.1, ?_⟩
      simp [rdCrc, ht]

/-- **The encoder's frames, read by the Go decoder**: `|rs|` records, to the end of their frames. -/
theorem reach_frames {C : WalCodec} (hC : C.Ok) {bs : List w8} {fs : List (List w8)} (rs : List WalRec) :
    ∀ {off : Nat} {c : w32} {rest : List w8}, RecsFit C rs → ChainOk C c rs →
    bs.drop off = recFrames C rs ++ rest →
    Reach C (bs :: fs) off c (bs :: fs) (off + (recFrames C rs).length) (chainEnd C c rs) rs.length := by
  induction rs with
  | nil => intro off c rest _ _ _; simpa [recFrames_nil, chainEnd] using Reach.refl (C := C) (bs :: fs) off c
  | cons r rs ih =>
    intro off c rest hfit hch hbs
    rw [recFrames_cons, List.append_assoc] at hbs
    obtain ⟨c1, hd, hok, hc1⟩ := goDecode_frame (fs := fs) hC (hfit r (by simp)) hbs hch.1
    have hbs' : bs.drop (off + (frame (C.encRec r)).length) = recFrames C rs ++ rest := by
      rw [← List.drop_drop, hbs]
      exact List.drop_left' rfl
    have h := ih (fun r' h => hfit r' (by simp [h])) hch.2 hbs'
    have e : off + (recFrames C (r :: rs)).length =
        off + (frame (C.encRec r)).length + (recFrames C rs).length := by
      rw [recFrames_cons, List.length_append]; omega
    rw [e, List.length_cons]
    refine .step hd hok ?_
    rw [hc1]; exact h

/-- **At the end of a file that is not the last**, the next record is the next file's first. -/
theorem reach_next {C : WalCodec} {f g : List w8} {gs : List (List w8)} {off : Nat} {c : w32}
    (hf : f.length ≤ off) {t : List (List w8)} {o : Nat} {c' : w32} {n : Nat}
    (h : Reach C (g :: gs) 0 c t o c' (n + 1)) : Reach C (f :: g :: gs) off c t o c' (n + 1) := by
  cases h with
  | step hd hok hr =>
    refine .step ?_ hok hr
    have he : decRecStep C (g :: gs).isEmpty f off c = .eof := by
      unfold decRecStep; simp [List.length_drop]; omega
    unfold goDecode; rw [he]; exact hd

/-- **Intact files, then a last file holding the frames of `R` (at least one record)**: the reader's
loop reaches the end of `R`'s frames in the last file after every record. -/
theorem reach_files {C : WalCodec} (hC : C.Ok) (last : List w8) (R : List WalRec) (hR : R ≠ []) :
    ∀ (rss : List (List WalRec)) (c : w32), RecsFit C (rss.flatten ++ R) → ChainOk C c (rss.flatten ++ R) →
    recFrames C R <+: last →
    Reach C (rss.map (recFrames C) ++ [last]) 0 c [last] (recFrames C R).length
      (chainEnd C c (rss.flatten ++ R)) (rss.flatten.length + R.length)
  | [], c, hfit, hch, ⟨rest, hrest⟩ => by
    simp only [List.map_nil, List.nil_append, List.flatten_nil, List.length_nil, Nat.zero_add] at *
    have := reach_frames (fs := []) (bs := last) hC R (off := 0) (c := c) (rest := rest) hfit hch
      (by rw [List.drop_zero, hrest])
    simpa using this
  | rs :: rss, c, hfit, hch, hpre => by
    simp only [List.flatten_cons, List.append_assoc] at hfit hch
    rw [chainOk_append] at hch
    have hfit1 : RecsFit C rs := fun r hr => hfit r (List.mem_append_left _ hr)
    have hfit2 : RecsFit C (rss.flatten ++ R) := fun r hr => hfit r (List.mem_append_right _ hr)
    have ih := reach_files hC last R hR rss (chainEnd C c rs) hfit2 hch.2 hpre
    have h1 := reach_frames (fs := rss.map (recFrames C) ++ [last]) (bs := recFrames C rs) hC rs
      (off := 0) (c := c) (rest := []) hfit1 hch.1 (by simp)
    obtain ⟨g, gs, hgf⟩ : ∃ g gs, rss.map (recFrames C) ++ [last] = g :: gs := by
      cases h : rss.map (recFrames C) ++ [last] with
      | nil => simp at h
      | cons g gs => exact ⟨g, gs, rfl⟩
    rw [hgf] at h1 ih
    have hpos : 0 < rss.flatten.length + R.length := by
      have := List.length_pos_iff.2 hR; omega
    obtain ⟨k, hk⟩ : ∃ k, rss.flatten.length + R.length = k + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
    rw [hk] at ih
    have h2 := reach_next (f := recFrames C rs) (off := 0 + (recFrames C rs).length) (by omega) ih
    have h3 := reach_trans h1 h2
    rw [List.map_cons, List.cons_append, hgf, List.flatten_cons, List.append_assoc, chainEnd_append,
      List.length_append]
    rw [show rs.length + rss.flatten.length + R.length = rs.length + (k + 1) by omega]
    exact h3

end reach

end WalEnc
end EtcdGrove
end Perennial
