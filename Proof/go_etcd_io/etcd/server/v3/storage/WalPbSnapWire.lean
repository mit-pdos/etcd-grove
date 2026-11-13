/-
**The wire format of a `walpb.Snapshot`** (W6 of `notes/wal-fsext-plan.md`, `SaveSnapshot`'s content
model): what protobuf-go's `proto.Marshal` produces for a `walpb.Snapshot` (and the `raftpb.ConfState`
inside it), as a transparent Lean function of the message's wire content, as `WalPbWire.lean` is for
`walpb.Record`. Pure (no Go types, nor raft's models: the part `LinuxFs/` imports it, and raft's
`PbModel`/`PbSchema` exist twice, in the main tree and in the part); the content's model
(`SnapshotMetadataM`) and the registration of `walpb.Snapshot` belong to the part.

`server/storage/wal/walpb/record.proto` and raft's `raftpb/raft.proto` (both proto2) at the pins:

    message Snapshot {                       message ConfState {
      optional uint64 index = 1;               repeated uint64 voters          = 1;
      optional uint64 term  = 2;               repeated uint64 learners        = 2;
      optional raftpb.ConfState conf_state = 3; repeated uint64 voters_outgoing = 3;
    }                                          repeated uint64 learners_next   = 4;
                                               optional bool   auto_leave      = 5;
                                             }

protobuf-go writes a generated message's set fields in field-number order, then its unknown fields
verbatim; a proto2 optional scalar iff its pointer is non-nil (its tag, the value as a varint, a
`bool` as 0 or 1); a proto2 `repeated uint64` (not packed: proto2's default) as one tag and varint
per element, in order (an empty list, `nil` or not, writes nothing); a message field iff its pointer
is non-nil: its tag, the length of its encoding as a varint, the encoding. Every number is below 16,
so every tag is one byte. Checked against Go by `examples/stdlib/walpb` (`TestSnapshotEncoder`,
`TestSnapshotSchema`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.WalPbWire

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace WalEnc

/-- **A `raftpb.ConfState`'s wire content** (inside a `walpb.Snapshot`): the four lists (a list needs
no presence: an empty one encodes to nothing), `AutoLeave` nil or set, the unknown fields. -/
structure WalCsC where
  voters : List w64
  learners : List w64
  votersOutgoing : List w64
  learnersNext : List w64
  autoLeave : Option Bool
  uf : List w8
deriving DecidableEq

/-- **A `walpb.Snapshot`'s wire content**: `Index`, `Term` nil or set, `ConfState` nil or a message,
the unknown fields. -/
structure WalSnapC where
  index : Option w64
  term : Option w64
  confState : Option WalCsC
  uf : List w8
deriving DecidableEq

/-- A proto2 `repeated uint64` numbered `num`, not packed: a tag and a varint per element. -/
def repVarintField (num : Nat) (vs : List w64) : List w8 :=
  vs.flatMap (fun v => varintEnc (num * 8) ++ varintEnc (uint.nat v))

/-- **The bytes protobuf-go writes for a `raftpb.ConfState` holding `c`.** -/
def csEnc (c : WalCsC) : List w8 :=
  repVarintField 1 c.voters ++ repVarintField 2 c.learners ++ repVarintField 3 c.votersOutgoing ++
    repVarintField 4 c.learnersNext ++
    optVarintField 5 (c.autoLeave.map (fun b => if b then 1 else 0)) ++ c.uf

/-- **The bytes protobuf-go writes for a `walpb.Snapshot` holding `s`.** -/
def snapEnc (s : WalSnapC) : List w8 :=
  optVarintField 1 (s.index.map uint.nat) ++ optVarintField 2 (s.term.map uint.nat) ++
    optBytesField 3 (s.confState.map csEnc) ++ s.uf

/-- **protobuf's size of a `walpb.Snapshot`** (`proto.Size`): its encoding's length (`proto.Size` is
the length `Marshal` writes; checked by `TestSnapshotEncoder`). -/
def snapSize (s : WalSnapC) : Nat := (snapEnc s).length

/-- **`record.proto`'s `Snapshot` schema** (`UfWire.lean`): `index` 1 and `term` 2 varints,
`conf_state` 3 length-delimited. -/
def walSnapSchema : FieldSchema := [(1, [0]), (2, [0]), (3, [2])]

/-- **`raft.proto`'s `ConfState` schema**: the four repeated `uint64`s (varint, or packed:
protobuf-go's decoder takes both), `auto_leave` 5 a varint. -/
def walCsSchema : FieldSchema := [(1, [0, 2]), (2, [0, 2]), (3, [0, 2]), (4, [0, 2]), (5, [0])]

/-- Each level's schema and unknown fields: the snapshot's, then its conf state's. -/
def WalSnapC.levels (s : WalSnapC) : List (FieldSchema × List w8) :=
  (walSnapSchema, s.uf) :: (match s.confState with | none => [] | some c => [(walCsSchema, c.uf)])

theorem snapEnc_ne_of_index (s : WalSnapC) (h : s.index.isSome) : snapEnc s ≠ [] := by
  rcases s with ⟨_ | i, t, c, u⟩
  · simp at h
  · unfold snapEnc optVarintField
    have : varintEnc (1 * 8) = [W8 8] := by rw [varintEnc, dite_eq_left (by decide)]; rfl
    simp [this]

end WalEnc
end EtcdGrove
end Perennial
