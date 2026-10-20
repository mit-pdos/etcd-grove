---
upstream: none
checked: 2026-10-20
links:
  - etcd-io/raft#423 pr merged: removed gogoproto.nullable from ConfState; not about unknown fields
  - etcd-io/raft#432 pr merged: passes ConfState as a pointer; not about unknown fields
candidate: issues/upstream/raft-confstate-unknown-fields-panic/
---

# raft v3.7: a `ConfState` with an unknown field makes `newRaft` and snapshot restore panic

- **Status**: open (a reachable panic; not reported). Introduced with the move of raftpb to
  protobuf-go v2: gogoproto's raftpb kept no unknown fields and `Equivalent` compared with
  `reflect.DeepEqual` the fields it had.
- **Where** (etcd-io/raft v3.7.0, `b867cf13`; the same in the fork commit `509271dac` that
  `etc/goose.py`'s project `raft37` pins):
  - `raftpb/confstate.go:26-52` (`ConfState.Equivalent`, "returns a nil error if the inputs
    describe the same configuration"): it clones both sides, sorts their id slices, makes
    `AutoLeave` explicit and compares with `proto.Equal`, which also compares the messages'
    unknown fields (protobuf-go v1.36.11, `proto/equal.go`: "the same set of unknown fields
    values"; `internal/impl/equal.go:193`).
  - `util.go:320` (`assertConfStatesEquivalent`) panics (`l.Panic`) when `Equivalent` errs.
  - `raft.go:1928` (`raft.restore`, reached from `handleSnapshot` for a `MsgSnap` and from
    `RawNode`/`node` callers) and `raft.go:479` (`newRaft`, the storage's `InitialState`) compare
    the snapshot's (storage's) `ConfState` with the one raft builds from its tracker
    (`ProgressTracker.ConfState`, `tracker/tracker.go:148`), which has no unknown fields.
- **What happens**: a `ConfState` carrying a field this version of raftpb does not know -- one
  added by a newer raft, in a snapshot sent by a newer leader or left in storage before a
  downgrade -- describes the same configuration but is reported not equivalent, and the node
  panics: on receiving the snapshot, or at every restart (`newRaft`). Reproduction (in package
  `raft`, passes on v3.7.0): `issues/raft-confstate-unknown-fields-panic/confstate_unknown_fields_test.go`
  (`TestSnapshotConfStateUnknownFieldPanics`: `Equivalent` errs on two `ConfState`s with the same
  voters, one with an unknown varint field 99; a follower stepping a `MsgSnap` with it panics
  with "ConfStates not equivalent after sorting").
- **Expected**: `Equivalent` compares configurations ("the inputs describe the same
  configuration"), so unknown fields should not matter; protobuf's own compatibility rules keep
  unknown fields so that older readers tolerate newer writers.
- **How the proof handles it**: the conf state's ownership predicate requires no unknown fields
  (`Raft37/Proof/go_etcd_io/raft/v3/InvPb.lean`, `csPts`: `pbMsg raftpb.ConfState p []`), and
  `proto.EqualConfState.spec` (`Spec/google_golang_org/protobuf/proto/EqualConfState.lean`) is
  stated for two such conf states; `ConfState.Equivalent.spec` therefore covers conf states without
  unknown fields only. A later stage's `raft.restore`/`newRaft` specs inherit it as a premise on the
  snapshot's and the storage's conf state (raft v3.7 retarget, stage R1).
- **Possible fixes**: in `Equivalent`, drop the unknown fields of the clones before comparing
  (`cs1v.ProtoReflect().SetUnknown(nil)`), or compare the four sorted slices and `GetAutoLeave()`
  directly instead of `proto.Equal`.
- **Found**: 2026-10-15, the raft v3.7 retarget, stage R1 (stating `proto.Equal`'s trust-boundary
  spec for `ConfState.Equivalent`).
