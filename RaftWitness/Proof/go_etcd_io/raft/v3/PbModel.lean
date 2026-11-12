/-
The raftpb values as the model sees them (raft v3.7 retarget; stage R0 made `EntryM`,
`MessageM`, `ConfChangeSingleM`, stage R1 made the records final and added the snapshot's and
the hard state's: `notes/raft-retarget-plan.md`, "Design", D1, and its decisions on the open
questions). Until the retarget the protocol model (`Plog`, `CCModel`, `Protocol/*`) used the
Goose value of gogoproto's `raftpb.Entry` (a struct of four plain fields) as its entry, and
stored the pending read-index requests as Goose `raftpb.Message` values (reading their
`From'`). In raft v3.7 (protobuf-go v2) every raftpb message is a struct of pointers (each
scalar field a `*T`, nested messages pointers, repeated messages `[]*T`) and protobuf runtime
state, handled only through a pointer, so it is not a pure value any more.

Each record here is what the getters of a raftpb message return, field for field, with the
Go field's name primed (as gogoproto's Goose fields were, so the model's text ports by a type
rename); a nil field reads as zero, as the getters return it:

* `EntryM`: `GetTerm`, `GetIndex`, `GetType`, `GetData` of a `*pb.Entry`. `Data'` is
  the bytes (D6, stage R4: v3.7's `appendEntry` appends clones, whose `Data` is a fresh slice of
  the same bytes, so a clone's record is its original's; until then the slice); the slice is
  read-only for good (`InvPb.lean`'s `entPts`).
* `MessageM`: the scalar getters of a `*pb.Message`; its references (`Entries`, `Snapshot`,
  `Context`, `Responses`) are not in it (the ownership predicate holds them,
  `InvPb.lean`'s `msgOwn`).
* `ConfChangeSingleM`: `GetType()`, `GetNodeId()` of a `*pb.ConfChangeSingle`, the model of one
  conf change (`CCModel`, `InvConfchange`).
* `ConfStateM`, `SnapshotMetadataM`, `SnapshotM` (stage R1): a snapshot as `GetData()`,
  `GetMetadata()` read it, nested as the Go messages are (`sv.Metadata'.ConfState'.AutoLeave'`,
  `sv.Metadata'.Index'` read as the old Goose value's fields did); a nil `Metadata` or
  `ConfState` reads as the zero record, as the chained getters return zeros on nil. A snapshot
  is owned and cloned whole (`proto.Clone`), so its contents are values: `Data'` and the conf
  state's lists are the lists, not the slices.
* `HardStateM` (stage R1): `GetTerm()`, `GetVote()`, `GetCommit()` of a `*pb.HardState`.

The protobuf runtime's hidden fields (`state`, `sizeCache`, `unknownFields`) are in none of
them: they are the trust boundary's (`pbMsg`, `InvPb.lean`).
-/
module

public import Perennial.Proof.ProofPrelude
public import RaftWitness.Code.go_etcd_io.raft.v3

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open go_etcd_io.raft.v3

/-- A log entry as the model sees it: what `GetTerm()`, `GetIndex()`, `GetType()`,
`GetData()`, `GetSubterm()` of a `*pb.Entry` return (a nil field reads as zero). The subterm
(2026-10-19, witness support, `notes/raft-witness.md`) is the leader's subterm when it
appended the entry; `0` in a cluster without a witness. -/
structure EntryM [GooseExts] where
  mk ::
  Term' : w64
  Index' : w64
  Type' : raftpb.EntryType
  Data' : List w8
  Subterm' : w64

instance EntryM.zero_val [GooseExts] : ZeroVal EntryM :=
  ⟨EntryM.mk zeroValDef zeroValDef zeroValDef [] zeroValDef⟩

/-- A message's scalar fields as the model sees them: what `GetType()`, `GetTo()`, ...,
`GetRejectHint()` of a `*pb.Message` return. -/
structure MessageM [GooseExts] where
  mk ::
  Type' : raftpb.MessageType
  To' : w64
  From' : w64
  Term' : w64
  LogTerm' : w64
  Index' : w64
  Commit' : w64
  Vote' : w64
  Reject' : Bool
  RejectHint' : w64

instance MessageM.zero_val [GooseExts] : ZeroVal MessageM :=
  ⟨MessageM.mk zeroValDef zeroValDef zeroValDef zeroValDef zeroValDef zeroValDef zeroValDef
    zeroValDef zeroValDef zeroValDef⟩

/-- One conf change as the model sees it: `GetType()`, `GetNodeId()` of a
`*pb.ConfChangeSingle`. -/
structure ConfChangeSingleM [GooseExts] where
  mk ::
  Type' : raftpb.ConfChangeType
  NodeId' : w64

instance ConfChangeSingleM.zero_val [GooseExts] : ZeroVal ConfChangeSingleM :=
  ⟨ConfChangeSingleM.mk zeroValDef zeroValDef⟩

/-- A conf state as the model sees it: `GetVoters()`, `GetLearners()`, `GetVotersOutgoing()`,
`GetLearnersNext()` (the lists behind the slices) and `GetAutoLeave()` of a `*pb.ConfState`. -/
structure ConfStateM where
  mk ::
  Voters' : List w64
  Learners' : List w64
  VotersOutgoing' : List w64
  LearnersNext' : List w64
  AutoLeave' : Bool
  -- (2026-10-20, witness support) raft#168's `GetWitness()`, `0` for none (`GetWitnessOutgoing()`
  -- is `0` in every conf state the specs handle: no joint configuration with a witness)
  Witness' : w64

instance ConfStateM.zero_val : ZeroVal ConfStateM := ⟨ConfStateM.mk [] [] [] [] false (W64 0)⟩

/-- A snapshot's metadata as the model sees it: `GetConfState()` (a nil one reads as the zero
record), `GetIndex()`, `GetTerm()` of a `*pb.SnapshotMetadata`. -/
structure SnapshotMetadataM where
  mk ::
  ConfState' : ConfStateM
  Index' : w64
  Term' : w64

instance SnapshotMetadataM.zero_val [GooseExts] : ZeroVal SnapshotMetadataM :=
  ⟨SnapshotMetadataM.mk (ConfStateM.mk [] [] [] [] false (W64 0)) zeroValDef zeroValDef⟩

/-- A snapshot as the model sees it: `GetData()` (the bytes) and `GetMetadata()` (a nil one
reads as the zero record) of a `*pb.Snapshot`. -/
structure SnapshotM where
  mk ::
  Data' : List w8
  Metadata' : SnapshotMetadataM

instance SnapshotM.zero_val [GooseExts] : ZeroVal SnapshotM :=
  ⟨SnapshotM.mk [] (SnapshotMetadataM.mk (ConfStateM.mk [] [] [] [] false (W64 0)) zeroValDef zeroValDef)⟩

/-- A hard state as the model sees it: `GetTerm()`, `GetVote()`, `GetCommit()` of a
`*pb.HardState`. -/
structure HardStateM where
  mk ::
  Term' : w64
  Vote' : w64
  Commit' : w64

instance HardStateM.zero_val [GooseExts] : ZeroVal HardStateM :=
  ⟨HardStateM.mk zeroValDef zeroValDef zeroValDef⟩

/-- A read state as the model sees it (D6, stage R4): the Go struct `raft.ReadState`'s `Index`
and the bytes of its `RequestCtx` (etcd matches read states by `bytes.Equal`, so the bytes are
its identity). The fields are primed as the old Goose struct's were, so `⟨i, d⟩` ports. -/
structure ReadStateM where
  mk ::
  Index' : w64
  RequestCtx' : List w8

instance ReadStateM.zero_val [GooseExts] : ZeroVal ReadStateM :=
  ⟨ReadStateM.mk zeroValDef []⟩

end EtcdGrove
end Perennial
