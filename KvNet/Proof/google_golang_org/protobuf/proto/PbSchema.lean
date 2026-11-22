-- The copy for the part `KvNet/` of `RaftNoAx/Proof/google_golang_org/protobuf/proto/PbSchema.lean` (etc/copy-part.py; rerun it, do not edit).
/-
**The schema of each registered message type** (per-type message models, stage A, `[v6a]` 3):
`pbSchemaOf ty`, the level schema (`FieldSchema`, `UfWire.lean`) of the protobuf message type `ty`,
which the raft messages' hidden-field invariant (`pbMsg`, `InvPb.lean`) reads its unknown fields
against (`pbMsg_alloc` takes `ufWire (pbSchemaOf ty) uf`), and the registered instances' top
levels (`PbModelC.levels`) are stated at.

**The schemas are trusted** (the Scope's T, `[v6a]` 1; read each against the type's `.proto` and
its Go descriptor; since 2026-11-21 (protobuf stage 0', mit-pdos/etcd-grove#20) the schema
constants and `pbSchemaOf` are generated from the registered descriptors, `models/pbdesc` (the
descriptors protobuf-go runs on, the one descriptor source pbgen reads too), by
`etc/gen-pbschema.py` between its marker lines below, `--check` in `etc/gates.sh`; `TYPES` there
lists which types get a schema): an over-declared schema makes D1 false (a decoded message's
unknown fields are claimed `ufWire` at it), an under-declared one D2 (`Unmarshal (Marshal c) ≠ c`). A type not listed
here gets `[]`, the weakest schema (`ufWire s uf → ufWire [] uf`: every number is routed to the
unknown fields). (Until 2026-11-21 that was what `pbMsg` claimed of `HardState`: wal-item3 registers it,
`hsSchema`, `pbHsC_reg`.) (out_size B2, 2026-11-12, approved by
etcd-grove-81: `notes/confchange-schema-empty.md`) `ConfChange`, `ConfChangeSingle` and
`ConfChangeV2` have their real schemas, though no registration models them: `pbMsg` of them records
the decoder-routed form, which `proto.MarshalConfChange[V2]`'s round trip needs, and the decoders'
posts (`proto.UnmarshalConfChange*`, `pbutil.MustUnmarshalMessage`'s `ConfChange` case) claim it
(Go: `examples/pbschema/confchange_test.go`, `TestB2CCDecoderUf`, `TestB2MustUnmarshalCC`; the
descriptor check `etc/pbschema-check.py` reads these three against their descriptors too). Until
then they were `[]`, under which those round trips were false of objects with unknown fields.

Sources: `raftpb/raft.proto` at the fork's `565c2bd` (raft v3.7, proto2; every field number is
below 16, so every tag is one byte):
- `Entry` (`raft.proto:12-17`): `Type` 1, `Term` 2, `Index` 3 (varints), `Data` 4 (length-delimited).
- `Message` (`raft.proto:62-99`): `type` 1, `to` 2, `from` 3, `term` 4, `logTerm` 5, `index` 6,
  `commit` 8, `vote` 13, `reject` 10, `rejectHint` 11 (varints); `entries` 7, `snapshot` 9,
  `context` 12, `responses` 14 (length-delimited).
- `Snapshot` (`raft.proto:25-28`): `data` 1, `metadata` 2 (length-delimited).
- `SnapshotMetadata` (`raft.proto:19-23`): `conf_state` 1 (length-delimited), `index` 2, `term` 3
  (varints).
- `ConfState` (`raft.proto:127-142`): `voters` 1, `learners` 2, `voters_outgoing` 3,
  `learners_next` 4 (repeated `uint64`, proto2 so unpacked; the decoder takes both the unpacked
  varint and the packed `LEN`), `auto_leave` 5 (varint).
- `HardState` (`raft.proto:101-105`): `term` 1, `vote` 2, `commit` 3 (`optional uint64` varints;
  registered 2026-11-21, wal-item3, approved by the user 2026-11-20 as option (a): `pbHsC_reg`,
  `wal/RaftModel/PbHardState.lean`).
- `ConfChange` (`raft.proto:151-160`): `id` 1, `type` 2, `node_id` 3 (varints), `context` 4
  (length-delimited).
- `ConfChangeSingle` (`raft.proto:164-167`): `type` 1, `node_id` 2 (varints).
- `ConfChangeV2` (`raft.proto:201-205`): `transition` 1 (varint), `changes` 2, `context` 3
  (length-delimited).

And the WAL's two registered types (2026-11-15, the WAL in the main tree: their registrations
`pbRecordC_reg`, `pbSnapC_reg`, `wal/walpb/PbRecord.lean`, `PbSnapshot.lean`, are read by the
descriptor check like raftpb's): `server/storage/wal/walpb/record.proto` at the etcd fork's pin
`e115818f5` (proto2; every number below 16):
- `Record` (`record.proto:8-12`): `type` 1 (`int64`), `crc` 2 (`uint32`) (varints), `data` 3
  (length-delimited).
- `Snapshot` (`record.proto:15-20`): `index` 1, `term` 2 (`uint64` varints), `conf_state` 3 (a
  `raftpb.ConfState`, length-delimited; its schema is `csSchema`).
-/
module

public import Proof.google_golang_org.protobuf.proto.UfWire
public import KvNet.Code.go_etcd_io.raft.v3.raftpb
public import KvNet.Code.go_etcd_io.etcd.server.v3.storage.wal.walpb

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open go_etcd_io.raft.v3

-- BEGIN etc/gen-pbschema.py (from the registered descriptors, models/pbdesc: do not edit, rerun it)

/-- `raftpb.Entry` (`raft.proto`, proto2): 1 `Type` (optional enum raftpb.EntryType), 2 `Term`
(optional uint64), 3 `Index` (optional uint64), 4 `Data` (optional bytes). -/
def entrySchema : FieldSchema := [(1, [0]), (2, [0]), (3, [0]), (4, [2])]

/-- `raftpb.Message` (`raft.proto`, proto2): 1 `type` (optional enum raftpb.MessageType), 2 `to`
(optional uint64), 3 `from` (optional uint64), 4 `term` (optional uint64), 5 `logTerm` (optional
uint64), 6 `index` (optional uint64), 7 `entries` (repeated raftpb.Entry), 8 `commit` (optional
uint64), 9 `snapshot` (optional raftpb.Snapshot), 10 `reject` (optional bool), 11 `rejectHint`
(optional uint64), 12 `context` (optional bytes), 13 `vote` (optional uint64), 14 `responses`
(repeated raftpb.Message). -/
def msgSchema : FieldSchema :=
  [(1, [0]), (2, [0]), (3, [0]), (4, [0]), (5, [0]), (6, [0]), (7, [2]), (8, [0]), (9, [2]),
   (10, [0]), (11, [0]), (12, [2]), (13, [0]), (14, [2])]

/-- `raftpb.Snapshot` (`raft.proto`, proto2): 1 `data` (optional bytes), 2 `metadata` (optional
raftpb.SnapshotMetadata). -/
def snapSchema : FieldSchema := [(1, [2]), (2, [2])]

/-- `raftpb.SnapshotMetadata` (`raft.proto`, proto2): 1 `conf_state` (optional raftpb.ConfState), 2
`index` (optional uint64), 3 `term` (optional uint64). -/
def metaSchema : FieldSchema := [(1, [2]), (2, [0]), (3, [0])]

/-- `raftpb.ConfState` (`raft.proto`, proto2): 1 `voters` (repeated uint64, unpacked), 2 `learners`
(repeated uint64, unpacked), 3 `voters_outgoing` (repeated uint64, unpacked), 4 `learners_next`
(repeated uint64, unpacked), 5 `auto_leave` (optional bool). -/
def csSchema : FieldSchema := [(1, [0, 2]), (2, [0, 2]), (3, [0, 2]), (4, [0, 2]), (5, [0])]

/-- `raftpb.HardState` (`raft.proto`, proto2): 1 `term` (optional uint64), 2 `vote` (optional
uint64), 3 `commit` (optional uint64). -/
def hsSchema : FieldSchema := [(1, [0]), (2, [0]), (3, [0])]

/-- `raftpb.ConfChange` (`raft.proto`, proto2): 1 `id` (optional uint64), 2 `type` (optional enum
raftpb.ConfChangeType), 3 `node_id` (optional uint64), 4 `context` (optional bytes). -/
def ccSchema : FieldSchema := [(1, [0]), (2, [0]), (3, [0]), (4, [2])]

/-- `raftpb.ConfChangeSingle` (`raft.proto`, proto2): 1 `type` (optional enum
raftpb.ConfChangeType), 2 `node_id` (optional uint64). -/
def ccsSchema : FieldSchema := [(1, [0]), (2, [0])]

/-- `raftpb.ConfChangeV2` (`raft.proto`, proto2): 1 `transition` (optional enum
raftpb.ConfChangeTransition), 2 `changes` (repeated raftpb.ConfChangeSingle), 3 `context` (optional
bytes). -/
def cc2Schema : FieldSchema := [(1, [0]), (2, [2]), (3, [2])]

/-- `walpb.Record` (`record.proto`, proto2): 1 `type` (optional int64), 2 `crc` (optional uint32), 3
`data` (optional bytes). -/
def WalEnc.recSchema : FieldSchema := [(1, [0]), (2, [0]), (3, [2])]

/-- `walpb.Snapshot` (`record.proto`, proto2): 1 `index` (optional uint64), 2 `term` (optional
uint64), 3 `conf_state` (optional raftpb.ConfState). -/
def WalEnc.walSnapSchema : FieldSchema := [(1, [0]), (2, [0]), (3, [2])]

section schemas
variable [GooseExts] [GoGlobalContext]

/-- **The schema of a message type** (see the file header): `raftpb.Entry`'s, `raftpb.Message`'s,
`raftpb.Snapshot`'s, `raftpb.SnapshotMetadata`'s, `raftpb.ConfState`'s, `raftpb.HardState`'s,
`raftpb.ConfChange`'s, `raftpb.ConfChangeSingle`'s, `raftpb.ConfChangeV2`'s, `walpb.Record`'s,
`walpb.Snapshot`'s; `[]` for every other type. -/
def pbSchemaOf (ty : go.GoType) : FieldSchema :=
  open Classical in
  if ty = raftpb.Entry.ty then entrySchema
  else if ty = raftpb.Message.ty then msgSchema
  else if ty = raftpb.Snapshot.ty then snapSchema
  else if ty = raftpb.SnapshotMetadata.ty then metaSchema
  else if ty = raftpb.ConfState.ty then csSchema
  else if ty = raftpb.HardState.ty then hsSchema
  else if ty = raftpb.ConfChange.ty then ccSchema
  else if ty = raftpb.ConfChangeSingle.ty then ccsSchema
  else if ty = raftpb.ConfChangeV2.ty then cc2Schema
  else if ty = go_etcd_io.etcd.server.v3.storage.wal.walpb.Record.ty then WalEnc.recSchema
  else if ty = go_etcd_io.etcd.server.v3.storage.wal.walpb.Snapshot.ty then WalEnc.walSnapSchema
  else []

-- END etc/gen-pbschema.py

theorem pbSchemaOf_entry : pbSchemaOf raftpb.Entry.ty = entrySchema := by
  unfold pbSchemaOf; simp

theorem pbSchemaOf_message : pbSchemaOf raftpb.Message.ty = msgSchema := by
  unfold pbSchemaOf raftpb.Entry.ty raftpb.Message.ty; simp

theorem pbSchemaOf_snapshot : pbSchemaOf raftpb.Snapshot.ty = snapSchema := by
  unfold pbSchemaOf raftpb.Entry.ty raftpb.Message.ty raftpb.Snapshot.ty; simp

theorem pbSchemaOf_snapshotMetadata : pbSchemaOf raftpb.SnapshotMetadata.ty = metaSchema := by
  unfold pbSchemaOf raftpb.Entry.ty raftpb.Message.ty raftpb.Snapshot.ty raftpb.SnapshotMetadata.ty
  simp

theorem pbSchemaOf_confState : pbSchemaOf raftpb.ConfState.ty = csSchema := by
  unfold pbSchemaOf raftpb.Entry.ty raftpb.Message.ty raftpb.Snapshot.ty raftpb.SnapshotMetadata.ty
    raftpb.ConfState.ty
  simp

theorem pbSchemaOf_hardState : pbSchemaOf raftpb.HardState.ty = hsSchema := by
  unfold pbSchemaOf raftpb.Entry.ty raftpb.Message.ty raftpb.Snapshot.ty raftpb.SnapshotMetadata.ty
    raftpb.ConfState.ty raftpb.HardState.ty
  simp

end schemas

/-- **The Go type of a generated message struct** (the Lean struct `T` of a protobuf message, its
Go type `goTy`): how `pbMsg T` names its schema (`pbSchemaOf (PbGoType.goTy T)`). An instance per
message type the raft predicates hold a `pbMsg` of. -/
class PbGoType (T : Type) where
  goTy : go.GoType

section inst
variable [GooseExts] [GoGlobalContext]

instance : PbGoType raftpb.Entry := ⟨raftpb.Entry.ty⟩
instance : PbGoType raftpb.Message := ⟨raftpb.Message.ty⟩
instance : PbGoType raftpb.Snapshot := ⟨raftpb.Snapshot.ty⟩
instance : PbGoType raftpb.SnapshotMetadata := ⟨raftpb.SnapshotMetadata.ty⟩
instance : PbGoType raftpb.ConfState := ⟨raftpb.ConfState.ty⟩
instance : PbGoType raftpb.HardState := ⟨raftpb.HardState.ty⟩
instance : PbGoType raftpb.ConfChange := ⟨raftpb.ConfChange.ty⟩
instance : PbGoType raftpb.ConfChangeSingle := ⟨raftpb.ConfChangeSingle.ty⟩
instance : PbGoType raftpb.ConfChangeV2 := ⟨raftpb.ConfChangeV2.ty⟩

end inst

end EtcdGrove
end Perennial
