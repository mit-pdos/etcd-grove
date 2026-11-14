/- Lean-first (no Rocq counterpart).

# What `ReadAll`'s reader decodes from the running WAL's files (pure; W3/W5 of `notes/wal-fsext-plan.md`)

`ReadAll` (S/wal.go:512-596) reads, with a fresh decoder, the page-cache bytes of the WAL's segments
from the one `Open` selected (position `p` among the history's segments `A ++ [Sl]`) on: every
segment but the last holds exactly its frames (`WalAbsD.intact`), the last its frames then bytes
past them on which the reader accepts nothing (`hend`: zeros, or the frames found at the generation's
start ended there, `WalAbsD.tailStop`). Then the reader's records are exactly the WAL's records from
segment `p` on (`walDecodeFiles_running`), through `walDecodeFiles_core` (`p = 0`) and
`walDecodeFiles_suffix` (`p > 0`, a cut file: the decoder's CRC starts at 0 and the cut's CRC record
re-seeds it).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.SegPre
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.WalEncSuffix
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.WalEncSegsImg

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Fs WalEnc go_etcd_io.raft.v3

section decode
variable [GooseExts]

theorem chainSegs_appendR (C : WalCodec) :
    ∀ (c : w32) (A B : List (List (w64 × List w8))),
      chainSegs C c (A ++ B) = chainSegs C c A ++ chainSegs C (crcAfter C c A.flatten) B
  | c, [], B => by simp [chainSegs, crcAfter]
  | c, D :: A, B => by
    simp only [List.cons_append, chainSegs, List.flatten_cons]
    rw [chainSegs_appendR C (crcAfter C c D) A B]
    simp [crcAfter, List.foldl_append]

/-- **A cut history keeping every operation's records is the history.** -/
theorem histCut_of_le (M : WalMarshal) : ∀ (H : WalHist) (n : Nat),
    (H.flatMap (opDs M)).length ≤ n → histCut M H n = H
  | [], _, _ => rfl
  | o :: H, n, h => by
    simp only [List.flatMap_cons, List.length_append] at h
    simp only [histCut]
    rw [if_pos (by omega), histCut_of_le M H _ (by omega)]

/-- The records of the last segment of the WAL with segments `A ++ [Sl]`. -/
def lastRecs (C : WalCodec) (M : WalMarshal) (md : List w8) (A : List WalHist) (Sl : WalHist) :
    List WalRec :=
  chainRecs C (crcAfter C 0#32 (segsDs M md true [] A).flatten)
    (segHdrDs M md (if A = [] then true else false) A.flatten ++ Sl.flatMap (opDs M))

theorem chainSegs_snocR (C : WalCodec) (M : WalMarshal) (md : List w8) (A : List WalHist)
    (Sl : WalHist) :
    chainSegs C 0#32 (segsDs M md true [] (A ++ [Sl])) =
      chainSegs C 0#32 (segsDs M md true [] A) ++ [lastRecs C M md A Sl] := by
  rw [segsDs_snoc, chainSegs_snoc]; rfl

theorem recsOfSegs_snocR (C : WalCodec) (M : WalMarshal) (md : List w8) (A : List WalHist)
    (Sl : WalHist) :
    recsOfSegs C M md (A ++ [Sl]) = recsOfSegs C M md A ++ lastRecs C M md A Sl := by
  unfold recsOfSegs
  rw [← flatten_chainSegs, chainSegs_snocR, List.flatten_append, flatten_chainSegs]
  simp

theorem chainEnd_lastRecs (C : WalCodec) (M : WalMarshal) (md : List w8) (A : List WalHist)
    (Sl : WalHist) :
    chainEnd C (crcAfter C 0#32 (segsDs M md true [] A).flatten) (lastRecs C M md A Sl) =
      chainEnd C 0#32 (recsOfSegs C M md (A ++ [Sl])) := by
  rw [recsOfSegs_snocR, chainEnd_append]
  congr 1
  unfold recsOfSegs
  rw [chainEnd_chainRecs]

/-- **No collision on the running last file**: it starts with the last segment's frames and the
reader accepts nothing at their end. -/
theorem noCollision_running {C : WalCodec} {c0 : w32} {rs : List WalRec} {last : List w8}
    (hpre : recFrames C rs <+: last)
    (hend : ∀ r len c', decStep C true last (recFrames C rs).length (chainEnd C c0 rs) ≠ .accept r len c') :
    NoCollisionFrom C c0 rs last := by
  intro xs ys r len c' hxy hacc
  cases ys with
  | nil =>
    rw [List.append_nil] at hxy; subst hxy
    exact absurd hacc (hend r len c')
  | cons r' ys' =>
    refine ⟨r', ys', rfl, ?_⟩
    obtain ⟨t, ht⟩ := hpre
    rw [← hxy, recFrames_append, recFrames_cons] at ht
    rw [← ht]
    simp

/-- **The reader on the running WAL's files from segment `p` on** (see the file header): the WAL's
segments `A ++ [Sl]`, the files from `p ≤ |A|` on the frames of each segment of `A`, then `last`,
the last segment's frames followed by bytes the reader accepts nothing on. -/
theorem walDecodeFiles_running {C : WalCodec} (hC : C.Ok) (M : WalMarshal) (md : List w8)
    (A : List WalHist) (Sl : WalHist) (p : Nat) (hp : p ≤ A.length) (last : List w8)
    (hfit : RecsFit C (recsOfSegs C M md (A ++ [Sl])))
    (hpre : recFrames C (lastRecs C M md A Sl) <+: last)
    (hend : ∀ r len c', decStep C true last (recFrames C (lastRecs C M md A Sl)).length
      (chainEnd C 0#32 (recsOfSegs C M md (A ++ [Sl]))) ≠ .accept r len c') :
    (walDecodeFiles C (((chainSegs C 0#32 (segsDs M md true [] A)).drop p).map (recFrames C) ++ [last])
        0#32).recs =
      (recsOfSegs C M md (A ++ [Sl])).drop (recsOfSegs C M md (A.take p)).length := by
  have hnc : NoCollisionFrom C (crcAfter C 0#32 (segsDs M md true [] A).flatten)
      (lastRecs C M md A Sl) last := by
    apply noCollision_running hpre
    rw [chainEnd_lastRecs]; exact hend
  have hfull : ∀ (P' : WalHist) (first' : Bool),
      (chainRecs C (crcAfter C 0#32 (segsDs M md true [] A).flatten)
        (segHdrDs M md first' P' ++ Sl.flatMap (opDs M))).take
        ((segHdrDs M md first' P').length + ((Sl.take Sl.length).flatMap (opDs M)).length) =
      chainRecs C (crcAfter C 0#32 (segsDs M md true [] A).flatten)
        (segHdrDs M md first' P' ++ Sl.flatMap (opDs M)) := by
    intro P' first'
    rw [List.take_length, List.take_of_length_le]
    simp [length_chainRecs]
  have hseg0 : ∀ (rs : List WalRec), segFile C rs 0 = recFrames C rs := by
    intro rs; simp [segFile]
  have hzip : ∀ (L : List (List WalRec)),
      List.zipWith (fun rs z => segFile C rs z) L (List.replicate L.length 0) = L.map (recFrames C) := by
    intro L
    induction L with
    | nil => rfl
    | cons x L ih => simp only [List.length_cons, List.replicate_succ, List.zipWith_cons_cons, ih, hseg0, List.map_cons]
  rcases Nat.eq_zero_or_pos p with hp0 | hp0
  · -- From the first file.
    subst hp0
    have hfit' : RecsFit C (chainRecs C 0#32 (segsDs M md true [] (A ++ [Sl])).flatten) := hfit
    obtain ⟨n, hn, hdec⟩ := walDecodeFiles_core hC M md Sl Sl.length last A
      (List.replicate A.length 0) true [] 0#32 (by simp) (by simp) hfit'
      (by
        refine ⟨?_, ?_⟩
        · simp only [List.nil_append]
          rw [hfull]; exact hpre
        · simp only [List.nil_append]; exact hnc)
    have hint : intactFiles C M md true [] 0#32 A (List.replicate A.length 0) =
        (chainSegs C 0#32 (segsDs M md true [] A)).map (recFrames C) := by
      unfold intactFiles
      have := hzip (chainSegs C 0#32 (segsDs M md true [] A))
      rwa [length_chainSegs, length_segsDs] at this
    rw [List.drop_zero, ← hint, hdec, histCut_of_le M Sl n (by simpa using hn)]
    simp [recsOfSegs, segsDs, chainRecs]
  · -- From a cut file.
    have hpre' : A.take p ≠ [] := by
      intro h; rw [List.take_eq_nil_iff] at h
      rcases h with h | h
      · omega
      · subst h; simp at hp; omega
    have hA : A = A.take p ++ A.drop p := (List.take_append_drop p A).symm
    have hc0 : (chainSegs C 0#32 (segsDs M md true [] A)).drop p =
        chainSegs C (crcAfter C 0#32 (segsDs M md true [] (A.take p)).flatten)
          (segsDs M md false (A.take p).flatten (A.drop p)) := by
      have e1 : chainSegs C 0#32 (segsDs M md true [] A) =
          chainSegs C 0#32 (segsDs M md true [] (A.take p)) ++
          chainSegs C (crcAfter C 0#32 (segsDs M md true [] (A.take p)).flatten)
            (segsDs M md false (A.take p).flatten (A.drop p)) := by
        conv => lhs; rw [hA]
        rw [segsDs_append, if_neg hpre', chainSegs_appendR]
        simp
      rw [e1, List.drop_left' (by rw [length_chainSegs, length_segsDs]; simp; omega)]
    have hss : A.take p ++ A.drop p ++ [Sl] = A ++ [Sl] := by rw [← hA]
    have hfit' : RecsFit C (recsOfSegs C M md (A.take p ++ A.drop p ++ Sl :: [])) := by
      rw [hss]; exact hfit
    obtain ⟨n, hn, hdec⟩ := walDecodeFiles_suffix hC M md (A.take p) (A.drop p) Sl []
      (List.replicate (A.drop p).length 0) last Sl.length hpre' (by simp) (by simp) hfit'
      (by
        simp only [← hA]
        refine ⟨?_, ?_⟩
        · have hAne : A ≠ [] := fun h => hpre' (by rw [h]; simp)
          have e : (if A = [] then true else false) = false := if_neg hAne
          rw [hfull]
          unfold lastRecs at hpre; rw [e] at hpre; exact hpre
        · have hAne : A ≠ [] := fun h => hpre' (by rw [h]; simp)
          have e : (if A = [] then true else false) = false := if_neg hAne
          unfold lastRecs at hnc; rw [e] at hnc; exact hnc)
    have hint : intactFiles C M md false (A.take p).flatten
        (crcAfter C 0#32 (segsDs M md true [] (A.take p)).flatten) (A.drop p)
        (List.replicate (A.drop p).length 0) =
        ((chainSegs C 0#32 (segsDs M md true [] A)).drop p).map (recFrames C) := by
      unfold intactFiles
      rw [hc0]
      have := hzip (chainSegs C (crcAfter C 0#32 (segsDs M md true [] (A.take p)).flatten)
        (segsDs M md false (A.take p).flatten (A.drop p)))
      rwa [length_chainSegs, length_segsDs] at this
    rw [← hint, hdec, histCut_of_le M Sl n (by simpa using hn), hss]

end decode

end WalFs
end EtcdGrove
end Perennial
