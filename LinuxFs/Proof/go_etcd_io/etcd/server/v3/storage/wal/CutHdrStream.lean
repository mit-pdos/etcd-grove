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

/-- The encoder's CRC of a quiescent handle: the chain's end over every record. -/
theorem WalHS.crc_done (Mr : WalMarshal) (h : WalHS) (hr : h.rest = 0) :
    WalHS.crc Mr h = tailCrc Mr h.H h.md h.cuts := by
  unfold WalHS.crc tailCrc allRecs
  rw [hr, Nat.sub_zero, List.take_length]

theorem varintSize_le_succ' : ∀ n : Nat, varintSize n ≤ n + 1 := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    unfold varintSize
    rw [varintEnc]
    split
    · simp
    · simp only [List.length_cons]
      have := ih (n / 128) (by omega)
      unfold varintSize at this
      omega

/-- A record of a small type, any CRC, and data `d`: its size at most twice `d`'s and `2^34`. -/
theorem recSize_le (t : w64) (k : w32) (d : List w8) (ht : uint.nat t < 2 ^ 8) :
    recSize (recOf ⟨t, k, d⟩) ≤ 2 * d.length + 2 ^ 34 := by
  have h1 := varintSize_le_succ' (uint.nat t)
  have h2 := varintSize_le_succ' (uint.nat k)
  have h3 := varintSize_le_succ' d.length
  have h4 : uint.nat k < 2 ^ 32 := by unfold uint.nat; exact BitVec.isLt _
  by_cases hc : t = crcType ∧ d = []
  · simp only [recSize, recOf, if_pos hc, List.length_nil]; omega
  · simp only [recSize, recOf, if_neg hc, List.length_nil]; omega

/-- Its frame. -/
theorem frame_walRecEnc_le (t : w64) (k : w32) (d : List w8) (ht : uint.nat t < 2 ^ 8) :
    (frame (walRecEnc ⟨t, k, d⟩)).length ≤ 2 * d.length + 2 ^ 34 + 16 := by
  have := recSize_le t k d ht
  rw [frame_length, walRecEnc, recEnc_length]
  have h2 := framePad_lt (recSize (recOf ⟨t, k, d⟩))
  omega

/-- **The headers fit** ext4's maximum offset (`Seek`'s bound; below the encoder's record bound). -/
theorem cutHdrs_fit (Mr : WalMarshal) (md : List w8) (hs : HardStateM) (c : w32)
    (hsz : md.length + (Mr.encState hs).length < 2 ^ 42) :
    (recFrames walCodec (chainRecs walCodec c (cutHdrDs Mr md hs))).length ≤ 0xffffffff000 := by
  rw [cutHdrRecs_frames]
  have h1 := frame_walRecEnc_le crcType (hash.crc32.crc32c c []) [] (by decide)
  have h2 := frame_walRecEnc_le metadataType (hash.crc32.crc32c (hash.crc32.crc32c c []) md) md
    (by decide)
  have h3 := frame_walRecEnc_le stateType (hash.crc32.crc32c (hash.crc32.crc32c
    (hash.crc32.crc32c c []) md) (Mr.encState hs)) (Mr.encState hs) (by decide)
  simp only [List.length_nil] at h1
  split <;> simp only [List.length_append, List.length_nil] <;> omega

/-- A header record's size, below the encoder's bound. -/
theorem recSize_hdr (t : w64) (k : w32) (d : List w8) (ht : uint.nat t < 2 ^ 8)
    (hd : d.length < 2 ^ 45) : recSize (recOf ⟨t, k, d⟩) < 2 ^ 47 := by
  have := recSize_le t k d ht
  omega

end pure

end WalFs
end EtcdGrove
end Perennial

end
