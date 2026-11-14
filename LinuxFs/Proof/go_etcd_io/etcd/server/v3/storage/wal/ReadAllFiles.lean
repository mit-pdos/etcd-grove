/- Lean-first (no Rocq counterpart).

# The running WAL's files as `ReadAll` reads them (pure; W3/W5 of `notes/wal-fsext-plan.md`)

The page-cache bytes of the named segments from the `kk`-th on (`WalAbsD`: every segment but the
last its frames, durable; the last its stream up to `wr` and the bytes under it past `wr`), when the
last segment's stream is all written (`wr` its length) and no resize window is open on it
(`TailExact`): the reader's records are the WAL's from the segment `first + kk` on
(`walReadFiles_running`, over `walDecodeFiles_running`). Both premises hold of a WAL whose tail no
handle holds (no tail registered): `WalTailIdle`, the invariant law `ReadAll` takes (a hypothesis
until the invariant holds it; the plan's W3/W5 log, fourteenth session).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadAllDecode

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Fs WalEnc go_etcd_io.raft.v3

section files
variable [GooseExts]

/-- The bytes a reader of the segment `g` reads: the page cache's values. -/
def segImg (g : SegG) : List w8 := g.bs.map (·.1)

theorem getD_of_lt {α : Type} (l : List α) (b : Nat) (x : α) (h : b < l.length) :
    l.getD b x = l[b] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]

/-- **The last segment's bytes, its stream written**: its stream, then the bytes under it. -/
theorem tailLast_img {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay} {g : SegG}
    (h : TailLast C Mr d lay g) (hwr : lay.wr = (segStream C Mr d lay.cuts lay.cuts.length).length) :
    segImg g = segStream C Mr d lay.cuts lay.cuts.length ++
      lay.old.drop (segStream C Mr d lay.cuts lay.cuts.length).length := by
  obtain ⟨h1, -, h3, h4, h5, -⟩ := h
  generalize hS : segStream C Mr d lay.cuts lay.cuts.length = S at *
  apply List.ext_getElem
  · simp only [segImg, List.length_map, List.length_append, List.length_drop]; omega
  · intro b hb1 hb2
    simp only [segImg, List.length_map] at hb1
    have hx := h5 b (g.bs[b]'hb1) (List.getElem?_eq_getElem hb1)
    simp only [segImg, List.getElem_map]
    by_cases hbS : b < S.length
    · rw [List.getElem_append_left hbS]
      have hw : decide (b < lay.wr) = true := by simp; omega
      rw [hw] at hx
      rw [hx.val_w, getD_of_lt _ _ _ hbS]
    · rw [List.getElem_append_right (by omega), List.getElem_drop]
      have hw : decide (b < lay.wr) = false := by simp; omega
      have hs : decide (b < lay.so) = false := by simp; omega
      rw [hw, hs] at hx
      rw [hx.val_unw, getD_of_lt _ _ _ (by omega)]
      congr 1; omega

/-- **What `ReadAll`'s reader reads from the named segments from the `kk`-th on** (see the file
header). -/
theorem walReadFiles_running {C : WalCodec} (hC : C.Ok) {Mr : WalMarshal} {d : WalDur} {lay : WalLay}
    {ents : Ents} (hab : WalAbsD C Mr d lay ents) (hex : TailExact lay)
    (hwr : lay.wr = (segStream C Mr d lay.cuts lay.cuts.length).length) (kk : Nat)
    (hkk : kk < lay.segs.length) :
    (walDecodeFiles C ((lay.segs.drop kk).map segImg) 0#32).recs =
      (recsOfSegs C Mr d.metadata (segsOf (histM d) lay.cuts)).drop
        (recsOfSegs C Mr d.metadata ((segsOf (histM d) lay.cuts).take (lay.first + kk))).length := by
  have hne : lay.segs ≠ [] := hab.nonempty
  obtain ⟨-, -, hfl⟩ := hab.cuts
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
  have hstreamL : segStream C Mr d lay.cuts lay.cuts.length = recFrames C (lastRecs C Mr d.metadata A Sl) := by
    unfold segStream; rw [hrecs, ← hAl, ← hlenA, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
    simp
  have hstream : ∀ i (hi : i < A.length), segStream C Mr d lay.cuts i =
      recFrames C ((chainSegs C 0#32 (segsDs Mr d.metadata true [] A))[i]'(by omega)) := by
    intro i hi
    unfold segStream
    rw [hrecs, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
      List.getElem?_eq_getElem (by omega), Option.getD_some]
  -- The named segments.
  have hsegs : lay.segs = lay.segs.dropLast ++ [lay.segs.getLast hne] := (List.dropLast_concat_getLast _).symm
  generalize hgL : lay.segs.getLast hne = gL at hsegs
  have hgL' : lay.segs.getLast? = some gL := by rw [List.getLast?_eq_getLast hne, hgL]
  have hTL := hab.lastEx hex gL hgL'
  -- The last file.
  have himg := tailLast_img hTL hwr
  have hfiles : (lay.segs.drop kk).map segImg =
      ((chainSegs C 0#32 (segsDs Mr d.metadata true [] A)).drop (lay.first + kk)).map (recFrames C) ++
        [segImg gL] := by
    have hdl : lay.segs.dropLast.length + 1 = lay.segs.length := by
      rw [List.length_dropLast]; have := List.length_pos_iff.2 hne; omega
    conv => lhs; rw [hsegs]
    rw [List.drop_append_of_le_length (by omega), List.map_append, List.map_singleton]
    congr 1
    apply List.ext_getElem
    · simp only [List.length_map, List.length_drop, hlenA, hAl]; omega
    · intro j h1 h2
      simp only [List.length_map, List.length_drop] at h1
      simp only [List.getElem_map, List.getElem_drop]
      have hj : kk + j + 1 < lay.segs.length := by omega
      have hg : lay.segs[kk + j]? = some (lay.segs.dropLast[kk + j]'(by omega)) := by
        rw [List.getElem_dropLast]; exact List.getElem?_eq_getElem _
      have hint := hab.intact (kk + j) _ hj hg
      rw [segImg, hint, List.map_map]
      have e : (Prod.fst ∘ durB) = (id : w8 → w8) := rfl
      rw [e, List.map_id, hstream (lay.first + (kk + j)) (by omega)]
      congr 2; omega
  rw [hfiles, hsplit, List.take_append_of_le_length (by omega)]
  apply walDecodeFiles_running hC Mr d.metadata A Sl (lay.first + kk) (by omega) (segImg gL)
  · rw [← hsplit, ← hSs]; exact hab.fit
  · rw [himg, ← hstreamL]; exact List.prefix_append _ _
  · intro r len c'
    rw [← hstreamL, ← hsplit, ← hSs]
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

end files

end WalFs
end EtcdGrove
end Perennial
