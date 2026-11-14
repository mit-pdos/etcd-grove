/- Lean-first (no Rocq counterpart).

# The truncate supply's pure steps (I3b, `wal-tc10`; pure)

The invariant's pure parts (`WalsOk`, `DirKeysOk`) across the two steps of the tail's truncate at its
write position (`walTail_truncSup`, `TruncSup.lean`): the first (`rzStart_pure`, the tail announced,
`rzSeg`), the landing (`rzLand_pure`, `rzLand`), and a step that leaves the layout as it was
(`tailLay_self`: an abort, or the finish not landed, which keeps the in-flight layout).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.RzWals

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Fs WalEnc

section pure
variable [GooseExts]

/-- The layout with its own last segment and write position. -/
theorem tailLay_self {lay : WalLay} {pre : List SegG} {g : SegG} (hs : lay.segs = pre ++ [g]) :
    tailLay lay pre g lay.wr = lay := by
  cases lay; simp only [tailLay] at hs ⊢; rw [hs]

/-- `WalsOk` and the directory keys across a step that leaves the layout as it was. -/
theorem walsOk_self {C : WalCodec} {Mr : WalMarshal} {R : Roots} {jr : Ino} {s : AbsDiskState}
    {Ls : GMap GoString WalLay} {cl : List Claim} {n : Nat} {dir : GoString} {lay : WalLay}
    {pre : List SegG} {g : SegG} (hW : WalsOk C Mr R jr s Ls cl n) (hl : Ls !! dir = some lay)
    (hs : lay.segs = pre ++ [g]) :
    WalsOk C Mr R jr s (<[dir := tailLay lay pre g lay.wr]> Ls) cl n ∧
      (∀ K c, DirKeysOk C Mr jr s Ls cl n K c →
        DirKeysOk C Mr jr s (<[dir := tailLay lay pre g lay.wr]> Ls) cl n K c) := by
  rw [tailLay_self hs, GMap.insert_id Ls dir lay hl]
  exact ⟨hW, fun _ _ h => h⟩

/-- **The truncate's first step at the write position**: `WalsOk` and the directory keys of the
layout with the tail announced (`rzSeg`), from the old. -/
theorem rzStart_pure {C : WalCodec} (hC : C.Ok) {Mr : WalMarshal} {R : Roots} {jr : Ino}
    {s : AbsDiskState} {Ls : GMap GoString WalLay} {cl : List Claim} {n : Nat} {dir : GoString}
    {d : WalDur} {lay : WalLay} {pre : List SegG} {g0 : SegG} {k : Nat}
    (hW : WalsOk C Mr R jr s Ls cl n) (hd : s.wal !! dir = some d) (hl : Ls !! dir = some lay)
    (hs : lay.segs = pre ++ [g0]) (habs : ∃ ents, WalAbsD C Mr d lay ents)
    (hcut : g0.om.cut = none) (hZ : TailZeros lay) (hB : TailBound C Mr d lay) (hk : 0 < k)
    (htcz : g0.om.TcZ) (hlo : ¬ SegExact g0 → g0.om.lo ≤ lay.wr) :
    WalsOk C Mr R jr s (<[dir := tailLay lay pre (rzSeg g0 true lay.wr k) lay.wr]> Ls) cl n ∧
      (∀ K c, DirKeysOk C Mr jr s Ls cl n K c →
        DirKeysOk C Mr jr s (<[dir := tailLay lay pre (rzSeg g0 true lay.wr k) lay.wr]> Ls) cl n K c) := by
  obtain ⟨ents, habs⟩ := habs
  have hnd : (lay.segs.map (·.ino)).Nodup := ((segsAll_nodup_iff Ls).1 hW.2.2.1).1 dir lay hl
  have hstep := tailCrashStep_rzStart (cl := cl) (k := n) hC habs hZ hB hnd hs hk htcz hlo
  refine ⟨walsOk_tailA hW hd hl hs rfl (by simp [rzSeg, hcut]) (fun ents' h => ?_) hstep,
    fun K c h => dirKeysOk_tailA hd hl hstep h⟩
  obtain ⟨hsz, -, -, hhi, -⟩ := h.metas g0 (by rw [hs]; simp)
  obtain ⟨-, -, -, hwb, -⟩ := h.lastWin g0 (by rw [hs]; simp)
  exact walAbsD_rzStart h hs (Nat.le_refl _) (Nat.min_le_right _ _) (by omega)
    (segBytesX_rzSeg hk (by omega) hsz.symm (by omega) htcz.1)

/-- **The truncate's landing at the write position**: `WalsOk` and the directory keys of the layout
with the tail landed (`rzLand`), from the in-flight one. -/
theorem rzLand_pure {C : WalCodec} {Mr : WalMarshal} {R : Roots} {jr : Ino}
    {s : AbsDiskState} {Ls : GMap GoString WalLay} {cl : List Claim} {n : Nat} {dir : GoString}
    {d : WalDur} {lay : WalLay} {pre : List SegG} {g0 : SegG} {k : Nat}
    (hW : WalsOk C Mr R jr s Ls cl n) (hd : s.wal !! dir = some d) (hl : Ls !! dir = some lay)
    (hs : lay.segs = pre ++ [rzSeg g0 true lay.wr k])
    (hlen : g0.bs.length = g0.om.size) (hwr : lay.wr ≤ g0.om.size) (hhi : g0.om.size ≤ g0.om.hi)
    (hcut : g0.om.cut = none) :
    WalsOk C Mr R jr s (<[dir := tailLay lay pre (rzLand g0 lay.wr k) lay.wr]> Ls) cl n ∧
      (∀ K c, DirKeysOk C Mr jr s Ls cl n K c →
        DirKeysOk C Mr jr s (<[dir := tailLay lay pre (rzLand g0 lay.wr k) lay.wr]> Ls) cl n K c) := by
  have hnd : (lay.segs.map (·.ino)).Nodup := ((segsAll_nodup_iff Ls).1 hW.2.2.1).1 dir lay hl
  have hstep := tailCrashStep_rzLand (C := C) (Mr := Mr) (d := d) (cl := cl) (k := n) hnd hs hlen hwr hhi
  refine ⟨walsOk_tailA hW hd hl hs rfl ?_ (fun ents h => walAbsD_rzLand h hs hlen hwr hcut hhi) hstep,
    fun K c h => dirKeysOk_tailA hd hl hstep h⟩
  simp [rzLand, rsPostK, rsPost, OsMeta.announce, hcut]

end pure

end WalFs
end EtcdGrove
end Perennial

end
