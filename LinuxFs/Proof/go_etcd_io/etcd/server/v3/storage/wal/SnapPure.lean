/- Lean-first (no Rocq counterpart).

# `SaveSnapshot`'s pure facts (W6; `WAL__SaveSnapshot.lean`)

`SaveSnapshot` commits `snap md` on the unsealed handle (`walTail_append`: its `w.snapi` is raised after
the encode, so the committed handle's `walMaxSnapIdx ≤ snapi` fails in between), encodes the snapshot
record, raises `w.snapi`/`w.enti` to the snapshot's index when below, and syncs. The quiescent handle
after the encode: `WalHS.split_snap` (its stream split and CRC, from the old ones and the encoder's
post), `snap_idx` (its index facts), `snap_guard` (the encode's guard: the old stream and the new frame
are a prefix of the new tail's stream).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.HandleAppend

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open WalEnc

section pure
variable [GooseExts]

theorem snapshotType_ne_crcType : snapshotType ≠ crcType := by decide

/-- The snapshot record the encoder writes after the chain's CRC `c`. -/
def snapRec (Mr : WalMarshal) (c : w32) (md : SnapshotMetadataM) : WalRec :=
  ⟨snapshotType, hash.crc32.crc32c c (Mr.encSnap md), Mr.encSnap md⟩

theorem tailRecs_snap (Mr : WalMarshal) (h : WalHS) (md : SnapshotMetadataM)
    (hc : ∀ b ∈ h.cuts, b ≤ h.H.length) (hr : h.rest = 0) :
    tailRecs Mr (h.H ++ [WalOpG.snap md]) h.md h.cuts =
      tailRecs Mr h.H h.md h.cuts ++ [snapRec Mr (h.crc Mr) md] := by
  rw [tailRecs_snoc Mr h.H h.md h.cuts _ hc]
  have : h.crc Mr = chainEnd walCodec 0#32 (allRecs Mr h.H h.md h.cuts) := by
    unfold WalHS.crc; rw [hr, Nat.sub_zero, List.take_length]
  rw [this]
  rfl

theorem allRecs_snap (Mr : WalMarshal) (h : WalHS) (md : SnapshotMetadataM)
    (hc : ∀ b ∈ h.cuts, b ≤ h.H.length) (hr : h.rest = 0) :
    allRecs Mr (h.H ++ [WalOpG.snap md]) h.md h.cuts =
      allRecs Mr h.H h.md h.cuts ++ [snapRec Mr (h.crc Mr) md] := by
  rw [allRecs_snoc Mr h.H h.md h.cuts _ hc]
  have : h.crc Mr = chainEnd walCodec 0#32 (allRecs Mr h.H h.md h.cuts) := by
    unfold WalHS.crc; rw [hr, Nat.sub_zero, List.take_length]
  rw [this]
  rfl

/-- **The quiescent handle after the snapshot record's encode** (see the file header). -/
theorem WalHS.split_snap (Mr : WalMarshal) (h : WalHS) (md : SnapshotMetadataM)
    (hc : ∀ b ∈ h.cuts, b ≤ h.H.length) (hs : h.Split Mr) (hr : h.rest = 0)
    (out' pend' : List w8) (sz' : Nat) (snapi' enti' : w64)
    (he : out' ++ pend' = h.out ++ h.pend ++ frame (walRecEnc (snapRec Mr (h.crc Mr) md))) :
    WalHS.Split Mr { h with H := h.H ++ [WalOpG.snap md], out := out', pend := pend', sz := sz', snapi := snapi', enti := enti' } ∧
    WalHS.crc Mr { h with H := h.H ++ [WalOpG.snap md], out := out', pend := pend', sz := sz', snapi := snapi', enti := enti' } = hash.crc32.crc32c (h.crc Mr) (Mr.encSnap md) := by
  have hE : h.encRecs Mr = tailRecs Mr h.H h.md h.cuts := by
    unfold WalHS.encRecs; rw [hr, Nat.sub_zero, List.take_length]
  have hE' : WalHS.encRecs Mr { h with H := h.H ++ [WalOpG.snap md], out := out', pend := pend', sz := sz', snapi := snapi', enti := enti' } =
      tailRecs Mr h.H h.md h.cuts ++ [snapRec Mr (h.crc Mr) md] := by
    unfold WalHS.encRecs; simp only; rw [hr, Nat.sub_zero, List.take_length, tailRecs_snap Mr h md hc hr]
  obtain ⟨h1, h2, -⟩ := hs
  rw [hE] at h1 h2
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rw [hE', recFrames_append]
    simp only
    rw [List.take_append_of_le_length h2, List.append_assoc, he]
    have : recFrames walCodec [snapRec Mr (h.crc Mr) md] = frame (walRecEnc (snapRec Mr (h.crc Mr) md)) := by
      simp [recFrames, frames]; rfl
    rw [this]
    conv => rhs; rw [← h1]
    simp only [List.append_assoc]
  · rw [hE', recFrames_append, List.length_append]; simp only; omega
  · simp only; rw [hr]; exact Nat.zero_le _
  · have this0 : chainEnd walCodec 0#32 (allRecs Mr h.H h.md h.cuts) = h.crc Mr := by
      unfold WalHS.crc; rw [hr, Nat.sub_zero, List.take_length]
    have key : WalHS.crc Mr { h with H := h.H ++ [WalOpG.snap md], out := out', pend := pend', sz := sz', snapi := snapi', enti := enti' } = chainEnd walCodec 0#32 (allRecs Mr (h.H ++ [WalOpG.snap md]) h.md h.cuts) := by
      unfold WalHS.crc; simp only; rw [hr, Nat.sub_zero, List.take_length]
    rw [key, allRecs_snap Mr h md hc hr, chainEnd_append, this0]
    show crcNext walCodec (h.crc Mr) (snapRec Mr (h.crc Mr) md) = _
    unfold crcNext
    rw [if_pos (show (snapRec Mr (h.crc Mr) md).typ ≠ crcType from snapshotType_ne_crcType)]
    rfl

/-- **The encode's guard**: everything the encoder holds, then the snapshot's frame, is the new tail's
stream past `o0`. -/
theorem snap_guard (Mr : WalMarshal) (h : WalHS) (md : SnapshotMetadataM)
    (hc : ∀ b ∈ h.cuts, b ≤ h.H.length) (hs : h.Split Mr) (hr : h.rest = 0) :
    h.out ++ h.pend ++ frame (walRecEnc (snapRec Mr (h.crc Mr) md)) =
      (tailStream Mr (h.H ++ [WalOpG.snap md]) h.md h.cuts).drop h.o0 := by
  have hE : h.encRecs Mr = tailRecs Mr h.H h.md h.cuts := by
    unfold WalHS.encRecs; rw [hr, Nat.sub_zero, List.take_length]
  obtain ⟨h1, h2, -⟩ := hs
  rw [hE] at h1 h2
  rw [tailStream_recs, tailRecs_snap Mr h md hc hr, recFrames_append, List.drop_append_of_le_length h2]
  have : recFrames walCodec [snapRec Mr (h.crc Mr) md] = frame (walRecEnc (snapRec Mr (h.crc Mr) md)) := by
    simp [recFrames, frames]; rfl
  rw [this]
  have hl : ((recFrames walCodec (tailRecs Mr h.H h.md h.cuts)).take h.o0).length = h.o0 := by
    rw [List.length_take]; omega
  conv => rhs; rw [← h1]
  rw [List.append_assoc, List.append_assoc, List.drop_left' hl, List.append_assoc]

/-- **The index facts after the snapshot record**, `w.snapi`/`w.enti` raised to its index when below. -/
theorem snap_idx (H : WalHist) (md : SnapshotMetadataM) (enti snapi : w64)
    (h1 : walLastIdx H ≤ max (uint.nat enti) (uint.nat snapi))
    (h2 : walMaxSnapIdx H ≤ uint.nat snapi) (hi : uint.nat md.Index' < 2 ^ 64 - 1)
    (hmax : max (uint.nat enti) (uint.nat snapi) + 1 < 2 ^ 64) :
    walLastIdx (H ++ [WalOpG.snap md]) ≤
        max (uint.nat (if uint.nat enti < uint.nat md.Index' then md.Index' else enti))
          (uint.nat (if uint.nat snapi < uint.nat md.Index' then md.Index' else snapi)) ∧
      walMaxSnapIdx (H ++ [WalOpG.snap md]) ≤
        uint.nat (if uint.nat snapi < uint.nat md.Index' then md.Index' else snapi) ∧
      max (uint.nat (if uint.nat enti < uint.nat md.Index' then md.Index' else enti))
        (uint.nat (if uint.nat snapi < uint.nat md.Index' then md.Index' else snapi)) + 1 < 2 ^ 64 := by
  have hl : walLastIdx (H ++ [WalOpG.snap md]) = max (walLastIdx H) (uint.nat md.Index') := by
    simp only [walLastIdx, List.foldl_append, List.foldl_cons, List.foldl_nil]; omega
  have hm : walMaxSnapIdx (H ++ [WalOpG.snap md]) = max (walMaxSnapIdx H) (uint.nat md.Index') := by
    simp [walMaxSnapIdx, List.foldl_append]
  rw [hl, hm]
  split <;> split <;> omega

end pure

end WalFs
end EtcdGrove
end Perennial

end
