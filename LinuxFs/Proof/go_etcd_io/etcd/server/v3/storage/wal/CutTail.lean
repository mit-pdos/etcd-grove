/- Lean-first (no Rocq counterpart).

# The tail record after a cut's rename (W2, `notes/wal-fsext-plan.md`, "W2 implementation log")

`cut`'s rename moves the handle's tail record (`walTailsRes`, `Inv.lean`) to the new segment: the
layout `cutLay lay |H| g wr` (`Cut.lean`), whose last segment is `g`, written and synced up to `wr`
(its headers' frames), zeros after (`old` all zeros, `z0 = 0`). Its per-tail facts:
`tailZeros_cut` (F-Z: `old` is zeros), `tailBound_cut` (the record boundary: `max so z0 = wr` ends
the new segment's records), `cutLay_last` (its last segment), and the record's value
(`tailG_cut`). Pure.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Inv
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CutLay

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Fs WalEnc

section cuttail
variable [GooseExts]

/-- The new segment is the cut layout's last. -/
theorem cutLay_last (lay : WalLay) (b : Nat) (g : SegG) (wr : Nat) :
    (cutLay lay b g wr).segs.getLast? = some g := by
  simp [cutLay]

/-- **F-Z after a cut**: the new segment's bytes before this generation's writes are zeros. -/
theorem tailZeros_cut (lay : WalLay) (b : Nat) (g : SegG) (wr : Nat) :
    TailZeros (cutLay lay b g wr) := by
  intro i _ hi
  simp only [cutLay, List.length_replicate] at hi ⊢
  simp [List.getD_eq_getElem?_getD, hi]

/-- **The record boundary after a cut**: the new segment synced at the end of its records (`wr`, its
headers' frames), `z0 = 0`. -/
theorem tailBound_cut (C : WalCodec) (Mr : WalMarshal) (d : WalDur) (lay : WalLay) (g : SegG)
    (wr : Nat)
    (hwr : wr = (segStream C Mr d (lay.cuts ++ [d.H.length]) (lay.cuts.length + 1)).length) :
    TailBound C Mr d (cutLay lay d.H.length g wr) := by
  refine ⟨((segRecs C Mr d (lay.cuts ++ [d.H.length])).getD (lay.cuts.length + 1) []).length,
    ?_, ?_⟩
  · simp [cutLay]
  · simp only [cutLay, List.length_append, List.length_singleton, List.take_length, Nat.max_zero]
    rw [hwr]
    rfl

/-- The tail record's value at the cut layout: the cuts extended, the write position `wr`, the new
segment's inode, no write in flight. -/
theorem tailG_cut (d : WalDur) (lay : WalLay) (g : SegG) (wr : Nat) :
    tailG d (cutLay lay d.H.length g wr) g.ino none =
      (d.H, d.metadata, lay.cuts ++ [d.H.length], wr, g.ino, none) := rfl

end cuttail

end WalFs
end EtcdGrove
end Perennial

end
