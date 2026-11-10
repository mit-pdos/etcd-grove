/-
**The schema of each registered message type** (per-type message models, stage A, `[v6a]` 3):
`pbSchemaOf ty`, the level schema (`FieldSchema`, `UfWire.lean`) of the protobuf message type `ty`,
which the raft messages' hidden-field invariant (`pbMsg`, `InvPb.lean`) reads its unknown fields
against (`pbMsg_alloc` takes `ufWire (pbSchemaOf ty) uf`), and the registered instances' top
levels (`PbModelC.levels`) are stated at.

**The schemas are trusted** (the Scope's T, `[v6a]` 1; read each against the type's `.proto` and
its Go descriptor): an over-declared schema makes D1 false (a decoded message's unknown fields are
claimed `ufWire` at it), an under-declared one D2 (`Unmarshal (Marshal c) ≠ c`). A type not listed
here gets `[]`, the weakest schema (`ufWire s uf → ufWire [] uf`: every number is routed to the
unknown fields): that is what `pbMsg` claims of `HardState`, `ConfChange`, `ConfChangeSingle` and
`ConfChangeV2`, which no registration models at their wire content (a schema there would make
today's `proto.UnmarshalConfChange*` axioms, whose posts hold `pbMsg`, claim D1 at it).

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
-/
module

public import Proof.google_golang_org.protobuf.proto.UfWire
public import Code.go_etcd_io.raft.v3.raftpb

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open go_etcd_io.raft.v3

/-- `raft.proto:12-17`. -/
def entrySchema : FieldSchema := [(1, [0]), (2, [0]), (3, [0]), (4, [2])]

/-- `raft.proto:62-99`. -/
def msgSchema : FieldSchema :=
  [(1, [0]), (2, [0]), (3, [0]), (4, [0]), (5, [0]), (6, [0]), (7, [2]), (8, [0]), (9, [2]),
   (10, [0]), (11, [0]), (12, [2]), (13, [0]), (14, [2])]

/-- `raft.proto:25-28`. -/
def snapSchema : FieldSchema := [(1, [2]), (2, [2])]

/-- `raft.proto:19-23`. -/
def metaSchema : FieldSchema := [(1, [2]), (2, [0]), (3, [0])]

/-- `raft.proto:127-142`: the repeated `uint64`s unpacked (`0`) or packed (`2`). -/
def csSchema : FieldSchema := [(1, [0, 2]), (2, [0, 2]), (3, [0, 2]), (4, [0, 2]), (5, [0])]

section schemas
variable [GooseExts] [GoGlobalContext]

/-- **The schema of a message type** (see the file header): the registered raftpb types', `[]`
for every other type. -/
def pbSchemaOf (ty : go.GoType) : FieldSchema :=
  open Classical in
  if ty = raftpb.Entry.ty then entrySchema
  else if ty = raftpb.Message.ty then msgSchema
  else if ty = raftpb.Snapshot.ty then snapSchema
  else if ty = raftpb.SnapshotMetadata.ty then metaSchema
  else if ty = raftpb.ConfState.ty then csSchema
  else []

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
