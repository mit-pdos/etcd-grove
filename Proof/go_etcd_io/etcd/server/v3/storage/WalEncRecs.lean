/-
**The records a WAL's history writes, and what a crash image of them decodes to** (pure; W1 of
`notes/wal-fsext-plan.md`, §2.2-§2.3). The Go reference is the WAL at the pin (fork commit
`0b50f04262d9`): `Create` (wal.go:169-183: `saveCrc(0)`, the metadata record,
`SaveSnapshot({Index: 0, Term: 0})`), `Save` (:1093-1135: `saveEntry` per entry, then `saveState`
unless the hard state is empty, :1072-1091), `SaveSnapshot` (:1137-1162), `encode`
(encoder.go:66-98: the record's CRC is the chain's after its data, a CRC record's data nil).

One segment (the first file, no cut): `recsOf` is the records of the first file of a WAL whose
history `H` was written without a cut, `streamOf` their frames. The cut's headers (CRC, metadata,
state, wal.go:914-924) are for the multi-file stream.

The map from an accepted record prefix back to a history (`histCut`) is not a parse: it cuts `H` at
the prefix's length (the plan's §2.2), which is `walImg`'s shape.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.WalEncDecode
public import Proof.go_etcd_io.etcd.server.v3.storage.WalHist

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalEnc

open go_etcd_io.raft.v3

section recs
variable [GooseExts]

/-- **The marshalled payloads** (parameters: protobuf's models live elsewhere). `encEntry e`:
`pbutil.MustMarshalMessage(e)` of the entry (`saveEntry`, wal.go:1074); `encState h`: of the hard
state (`saveState`, :1088); `encSnap m`: of the `walpb.Snapshot` `SaveSnapshot` is given for the
history's `.snap m` (:1145); `snap0`: of `walpb.Snapshot{Index: 0, Term: 0}` (`Create`, :181). -/
structure WalMarshal where
  encEntry : EntryM → List w8
  encState : HardStateM → List w8
  encSnap : SnapshotMetadataM → List w8
  snap0 : List w8

instance : DecidablePred hsEmptyP := fun h => by unfold hsEmptyP; infer_instance

/-- **An operation's records**, as (type, data): `Save(h, es)` an entry record per entry, then the
state record unless `h` is empty (`saveState`, wal.go:1084; `Save`'s shortcut, :1098, writes
nothing when both are empty, which this gives too); `SaveSnapshot(m)` one snapshot record. -/
def opDs (M : WalMarshal) : WalOp → List (w64 × List w8)
  | .save h es => es.map (fun e => (entryType, M.encEntry e)) ++
      (if hsEmptyP h then [] else [(stateType, M.encState h)])
  | .snap m => [(snapshotType, M.encSnap m)]

/-- **The first file's header records** (`Create`, wal.go:174-183): the CRC record (data nil), the
metadata `md`, the initial snapshot record. -/
def hdrDs (M : WalMarshal) (md : List w8) : List (w64 × List w8) :=
  [(crcType, []), (metadataType, md), (snapshotType, M.snap0)]

/-- **The encoder's CRCs** (encoder.go:74-75): each record carries the chain's CRC after its data,
from the encoder's initial CRC `c`. -/
def chainRecs (C : WalCodec) : w32 → List (w64 × List w8) → List WalRec
  | _, [] => []
  | c, (t, d) :: ds => ⟨t, C.crc32c c d, d⟩ :: chainRecs C (C.crc32c c d) ds

/-- **The records of a WAL with metadata `md` and history `H`**, in one file (`Create`'s encoder
starts at CRC 0, wal.go:169). -/
def recsOf (C : WalCodec) (M : WalMarshal) (md : List w8) (H : WalHist) : List WalRec :=
  chainRecs C 0#32 (hdrDs M md ++ H.flatMap (opDs M))

/-- **The bytes the records are written as** (the page writer's output, in order). The file then
holds the preallocated zeros (`streamOf … ++ List.replicate z 0`). -/
def streamOf (C : WalCodec) (M : WalMarshal) (md : List w8) (H : WalHist) : List w8 :=
  recFrames C (recsOf C M md H)

/-- **The history a record count cuts `H` to** (§2.2): the operations whose records all fit in `n`
op records, then, if `n` ends inside a `Save`, the `Save` of its first entries with the empty hard
state (its state record, written last, is not in). -/
def histCut (M : WalMarshal) : WalHist → Nat → WalHist
  | [], _ => []
  | o :: H, n =>
    if (opDs M o).length ≤ n then o :: histCut M H (n - (opDs M o).length)
    else match o with
      | .save _ es => if n = 0 then [] else [.save hsZero (es.take n)]
      | .snap _ => []

/-! ## The lemmas -/

/-- The encoder's records are a chain the reader accepts. -/
theorem chainOk_chainRecs {C : WalCodec} (hC : C.Ok) (c : w32) (ds : List (w64 × List w8))
    (hds : ∀ p ∈ ds, p.1 = crcType → p.2 = []) : ChainOk C c (chainRecs C c ds) := by
  sorry

theorem chainOk_recsOf {C : WalCodec} (hC : C.Ok) (M : WalMarshal) (md : List w8) (H : WalHist) :
    ChainOk C 0#32 (recsOf C M md H) := by
  sorry

/-- **(a) What the encoder wrote decodes to its records**, then the preallocated zeros read as the
end (`io.EOF`). -/
theorem walDecode_streamOf {C : WalCodec} (hC : C.Ok) (M : WalMarshal) (md : List w8) (H : WalHist)
    (hfit : RecsFit C (recsOf C M md H)) {z : Nat} (hz : z = 0 ∨ 8 ≤ z) :
    (walDecode C (streamOf C M md H ++ List.replicate z (0#8))).recs = recsOf C M md H ∧
    (walDecode C (streamOf C M md H ++ List.replicate z (0#8))).stop = .eof := by
  sorry

/-- The records of a cut history are a prefix of the records. -/
theorem recsOf_histCut (C : WalCodec) (M : WalMarshal) (md : List w8) (H : WalHist) (n : Nat) :
    recsOf C M md (histCut M H n) = (recsOf C M md H).take (3 + n) := by
  sorry

/-- **(c) A cut history is an image** (`walImg`) when it keeps the first `m` operations' records. -/
theorem walImg_histCut (M : WalMarshal) (H : WalHist) (m n : Nat) (hm : m ≤ H.length)
    (hn : ((H.take m).flatMap (opDs M)).length ≤ n) : walImg H m (histCut M H n) := by
  sorry

/-- **(b) + (c) What a crash image decodes to**: an image that starts with the bytes of the first
`m` operations (synced) and has no collision with the intended stream decodes to the records of an
image `I` of the history, `walImg H m I`. -/
theorem walDecode_walImg {C : WalCodec} (hC : C.Ok) (M : WalMarshal) (md : List w8) (H : WalHist)
    (m : Nat) (img : List w8) (hfit : RecsFit C (recsOf C M md H)) (hm : m ≤ H.length)
    (hdur : streamOf C M md (H.take m) <+: img) (hnc : NoCollision C (recsOf C M md H) img) :
    ∃ I, walImg H m I ∧ (walDecode C img).recs = recsOf C M md I := by
  sorry

end recs

end WalEnc
end EtcdGrove
end Perennial
