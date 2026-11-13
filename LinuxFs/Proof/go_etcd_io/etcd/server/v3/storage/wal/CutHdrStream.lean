/- Lean-first (no Rocq counterpart).

# The records of the segment a cut starts (W2, `cut`'s steps 5 and 8; pure)

`cut` (S/wal.go:875-965) starts a segment at the history's end: its records are a cut's headers
(`cutHdrDs`: the CRC record, the metadata, the state unless empty), chained from the encoder's CRC
after every record of the WAL (`tailCrc`, the `prevCrc` of `newFileEncoder`), and nothing else.

* `allRecs_cut`: the WAL's records after the cut are the old ones, then the headers.
* `tailRecs_cut`, `tailCrc_cut`: the new tail's records are the headers; the chain's end after them.
* `cutHdrRecs_frames`: the headers' frames, record by record, as `saveCrc`, `encode(Metadata)` and
  `saveState` write them.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Handle
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CutLay
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.SegPre
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.WalEncSegsImg

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Fs WalEnc

section pure
variable [GooseExts]

/-- `chainSegs` of a concatenation. -/
theorem chainSegs_append (C : WalCodec) :
    ∀ (c : w32) (A B : List (List (w64 × List w8))),
      chainSegs C c (A ++ B) = chainSegs C c A ++ chainSegs C (crcAfter C c A.flatten) B
  | c, [], B => by simp [chainSegs, crcAfter]
  | c, D :: A, B => by
    simp only [List.cons_append, chainSegs, List.flatten_cons]
    rw [chainSegs_append C (crcAfter C c D) A B]
    simp [crcAfter, List.foldl_append]

/-- The segments' records with a cut at the end: the old ones, then a cut's headers after the
whole history (the empty last segment). -/
theorem segsDs_cut (Mr : WalMarshal) (md : List w8) (H : WalHist) (cuts : List Nat)
    (hs : cuts.Pairwise (· ≤ ·)) (hle : ∀ b ∈ cuts, b ≤ H.length) :
    segsDs Mr md true [] (segsOf H (cuts ++ [H.length])) =
      segsDs Mr md true [] (segsOf H cuts) ++ [cutHdrDs Mr md (walLastHS H)] := by
  rw [segsOf_snoc_end, segsDs_append]
  have hne : segsOf H cuts ≠ [] := by
    intro h0; have := length_segsOf H cuts; rw [h0] at this; simp at this
  rw [if_neg hne, List.nil_append, segsOf_flatten H cuts hs hle]
  simp [segsDs, segHdrDs]

/-- The chain's end over the old records is the tail's CRC. -/
theorem crcAfter_tailCrc (Mr : WalMarshal) (H : List (WalOpG WalEnt)) (md : List w8)
    (cuts : List Nat) :
    crcAfter walCodec 0#32 (segsDs Mr md true [] (segsOf (H.map WalOpG.toM) cuts)).flatten =
      tailCrc Mr H md cuts := by
  unfold tailCrc recsOfSegs
  rw [chainEnd_chainRecs]

/-- **The WAL's records after the cut**: the old ones, then the headers chained from `tailCrc`. -/
theorem allRecs_cut (Mr : WalMarshal) (H : List (WalOpG WalEnt)) (md : List w8) (cuts : List Nat)
    (hs : cuts.Pairwise (· ≤ ·)) (hle : ∀ b ∈ cuts, b ≤ H.length) :
    allRecs Mr (H := H) md (cuts ++ [H.length]) = allRecs Mr H md cuts ++
      chainRecs walCodec (tailCrc Mr H md cuts) (cutHdrDs Mr md (walLastHS (H.map WalOpG.toM))) := by
  unfold allRecs recsOfSegs
  have hN : H.length = (H.map WalOpG.toM).length := by simp
  rw [hN, segsDs_cut Mr md _ cuts hs (by rw [← hN]; exact hle), List.flatten_append,
    chainRecs_append, crcAfter_tailCrc]
  simp

/-- **The new tail's records**: the headers. -/
theorem tailRecs_cut (Mr : WalMarshal) (H : List (WalOpG WalEnt)) (md : List w8) (cuts : List Nat)
    (hs : cuts.Pairwise (· ≤ ·)) (hle : ∀ b ∈ cuts, b ≤ H.length) :
    tailRecs Mr H md (cuts ++ [H.length]) =
      chainRecs walCodec (tailCrc Mr H md cuts) (cutHdrDs Mr md (walLastHS (H.map WalOpG.toM))) := by
  unfold tailRecs
  have hN : H.length = (H.map WalOpG.toM).length := by simp
  rw [hN, segsDs_cut Mr md _ cuts hs (by rw [← hN]; exact hle), chainSegs_append, crcAfter_tailCrc]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right
    (by rw [length_chainSegs, length_segsDs, length_segsOf]; simp)]
  rw [length_chainSegs, length_segsDs, length_segsOf]
  simp [chainSegs]

/-- **The chain's end after the cut**: after the headers. -/
theorem tailCrc_cut (Mr : WalMarshal) (H : List (WalOpG WalEnt)) (md : List w8) (cuts : List Nat)
    (hs : cuts.Pairwise (· ≤ ·)) (hle : ∀ b ∈ cuts, b ≤ H.length) :
    tailCrc Mr H md (cuts ++ [H.length]) =
      crcAfter walCodec (tailCrc Mr H md cuts) (cutHdrDs Mr md (walLastHS (H.map WalOpG.toM))) := by
  have hN : H.length = (H.map WalOpG.toM).length := by simp
  rw [← crcAfter_tailCrc Mr H md (cuts ++ [H.length]), ← crcAfter_tailCrc Mr H md cuts, hN,
    segsDs_cut Mr md _ cuts hs (by rw [← hN]; exact hle), List.flatten_append]
  simp [crcAfter, List.foldl_append]

/-- **The headers' frames**, record by record (`saveCrc`'s, `encode(Metadata)`'s, `saveState`'s),
from the encoder's CRC `c`. -/
theorem cutHdrRecs_frames (Mr : WalMarshal) (md : List w8) (hs : HardStateM) (c : w32) :
    recFrames walCodec (chainRecs walCodec c (cutHdrDs Mr md hs)) =
      frame (walRecEnc ⟨crcType, hash.crc32.crc32c c [], []⟩) ++
      frame (walRecEnc ⟨metadataType, hash.crc32.crc32c (hash.crc32.crc32c c []) md, md⟩) ++
      (if hsEmptyP hs then [] else
        frame (walRecEnc ⟨stateType, hash.crc32.crc32c (hash.crc32.crc32c (hash.crc32.crc32c c []) md)
          (Mr.encState hs), Mr.encState hs⟩)) := by
  unfold cutHdrDs
  split <;> simp [chainRecs, recFrames_cons, recFrames_nil, walCodec]

/-- The chain's CRC after the headers. -/
theorem crcAfter_cutHdrs (Mr : WalMarshal) (md : List w8) (hs : HardStateM) (c : w32) :
    crcAfter walCodec c (cutHdrDs Mr md hs) =
      if hsEmptyP hs then hash.crc32.crc32c (hash.crc32.crc32c c []) md else
        hash.crc32.crc32c (hash.crc32.crc32c (hash.crc32.crc32c c []) md) (Mr.encState hs) := by
  unfold cutHdrDs
  split <;> simp [crcAfter, walCodec]

end pure

end WalFs
end EtcdGrove
end Perennial

end
