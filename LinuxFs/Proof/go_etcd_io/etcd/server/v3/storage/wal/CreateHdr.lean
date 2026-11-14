/- Lean-first (no Rocq counterpart).

# `Create`'s first segment: its stream (W4, `notes/wal-fsext-plan.md`, "W4 implementation log"; pure)

The fresh WAL's one segment's intended bytes (`segStream … (walDurFresh md) [] 0`) are the frames of
`saveCrc(0)`'s, `encode(Metadata)`'s and `SaveSnapshot`'s records (`createStream_frames`, the snapshot's
data `Mr.snap0`, which `WalMarshalCreateOk` makes the object's encoding), a multiple of 8 long and
within ext4's maximum offset for metadata below `2^41` (`createStream_fit`).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CutHdrStream
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CutRen
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateSnap
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__SaveSnapshotPre

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Fs WalEnc

section pure
variable [GooseExts]

/-- **The fresh WAL's segment's stream.** -/
abbrev createStream (Mr : WalMarshal) (md : List w8) : List w8 :=
  segStream walCodec Mr (walDurFresh md) [] 0

/-- The stream is the frames of the header records from CRC 0. -/
theorem createStream_recs (Mr : WalMarshal) (md : List w8) :
    createStream Mr md = recFrames walCodec (chainRecs walCodec 0#32 (hdrDs Mr md)) := by
  simp [createStream, segStream, segRecs, segsDs, segsOf, histM, walDurFresh, segHdrDs, chainSegs]

/-- **The stream, record by record** (`saveCrc(0)`'s, `encode(Metadata)`'s, `SaveSnapshot`'s). -/
theorem createStream_frames (Mr : WalMarshal) (md : List w8) (hMr : WalMarshalCreateOk Mr) :
    createStream Mr md =
      frame (walRecEnc ⟨crcType, hash.crc32.crc32c 0#32 [], []⟩) ++
      frame (walRecEnc ⟨metadataType, hash.crc32.crc32c (hash.crc32.crc32c 0#32 []) md, md⟩) ++
      snapFrame Mr (hash.crc32.crc32c (hash.crc32.crc32c 0#32 []) md) snapC0.model := by
  rw [createStream_recs]
  unfold snapFrame
  rw [hMr.2]
  simp [hdrDs, chainRecs, recFrames_cons, recFrames_nil, walCodec]

/-- A multiple of 8 long. -/
theorem createStream_mod8 (Mr : WalMarshal) (md : List w8) : (createStream Mr md).length % 8 = 0 := by
  rw [createStream_recs]; exact recFrames_mod8 _ _

/-- **The stream fits** ext4's maximum offset, and its snapshot record below the encoder's bound. -/
theorem createStream_fit (Mr : WalMarshal) (md : List w8) (hMr : WalMarshalCreateOk Mr)
    (hmd : md.length < 2 ^ 41) : (createStream Mr md).length ≤ 0xffffffff000 := by
  rw [createStream_frames Mr md hMr]
  unfold snapFrame
  have h1 := frame_walRecEnc_le crcType (hash.crc32.crc32c 0#32 []) [] (by decide)
  have h2 := frame_walRecEnc_le metadataType (hash.crc32.crc32c (hash.crc32.crc32c 0#32 []) md) md
    (by decide)
  have h3 := frame_walRecEnc_le snapshotType (hash.crc32.crc32c (hash.crc32.crc32c
    (hash.crc32.crc32c 0#32 []) md) (Mr.encSnap snapC0.model)) (Mr.encSnap snapC0.model) (by decide)
  have h4 : (Mr.encSnap snapC0.model).length < 2 ^ 8 := by
    rw [hMr.2, hMr.1]; simp [snapC0, snapEnc, optVarintField, optBytesField, varintEnc]
  simp only [List.length_nil, List.length_append] at h1 ⊢
  omega

/-- At least one frame (8 bytes) long. -/
theorem createStream_pos (Mr : WalMarshal) (md : List w8) (hMr : WalMarshalCreateOk Mr) :
    8 ≤ (createStream Mr md).length := by
  rw [createStream_frames Mr md hMr]
  simp only [List.length_append, WalEnc.frame_length]
  omega

end pure

end WalFs
end EtcdGrove
end Perennial
