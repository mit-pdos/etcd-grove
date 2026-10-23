---
upstream: none
checked: 2026-10-23
links:
  - etcd-io/raft#168 pr open: related (draft since 2024-02, untouched since 2025-02: witness support, adds ConfState fields 6 and 7, `witness`/`witness_outgoing`; the only known proposal adding a ConfState field)
  - etcd-io/raft#133 issue open: related (the witness proposal #168 implements)
  - etcd-io/raft#423 pr merged: removed gogoproto.nullable from ConfState; not about unknown fields
  - etcd-io/raft#432 pr merged: passes ConfState as a pointer; not about unknown fields
candidate: issues/upstream/raft-confstate-unknown-fields-panic/
---

# raft v3.7: a `ConfState` with an unknown field makes `newRaft` and snapshot restore panic

- **Status**: not an issue today (review of 2026-10-23 below): a forward-compatibility regression
  with no field to trigger it; a reachable panic only once some raft adds a `ConfState` field. Introduced with the move of raftpb to
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

## Review, 2026-10-23: a real regression, but no realistic trigger; not an issue

Question: is there serious risk of a field being added to `ConfState`, and does other raft/etcd
code deal with unknown fields for compatibility? Checked at etcd-io/raft upstream `main`
`1931ff5` (2026-10-19) and etcd upstream `main` `3aaab3479b`.

- **(a) Fields are rarely added.** `ConfState` (`raftpb/raft.proto:127-142`) got `learners` (2) in
  `26506fa` (2017-11, "raft: support learner") and `voters_outgoing`/`learners_next`/`auto_leave`
  (3-5) in `277528e` (2019-07, "raft: introduce protos for joint quorums"); nothing since (7
  years; the 2026 commits only drop gogoproto options). The only proposal adding fields is the
  witness draft etcd-io/raft#168 (`witness = 6`, `witness_outgoing = 7`, plus a new
  `ConfChangeAddWitness`), open as a draft since 2024-02 and idle since 2025-02; its issue #133 has
  no maintainer commitment. A feature of that size would need a gated rollout anyway (old nodes
  cannot apply `ConfChangeAddWitness` either), so the `ConfState` field would not be the first
  incompatibility hit.
- **(b) Nothing else in raft or etcd handles unknown fields.** The original `Equivalent` (`e515a67`,
  2019-08) did clear them (`cs.XXX_unrecognized = nil` before `reflect.DeepEqual`; etcd
  `release-3.4` `raft/raftpb/confstate.go:38`), but `3a3d196` (2021-03) stopped generating
  `XXX_unrecognized` for all raft protos, arguing that "any real mixed-version upgrade story for
  this package is mostly untold", so gogoproto raft (v3.5-v3.6) silently dropped unknown fields.
  The v3.7 rewrite to protobuf-go (`4a0d945`, 2026-05-22, "*: enable vet to avoid copylock",
  `raftpb/confstate.go:31-48`) switched to `proto.Equal`, which compares the unknown fields
  protobuf-go now keeps: that is where the sensitivity comes back, as a side effect, not a
  decision. `Equivalent` (via `assertConfStatesEquivalent`, `util.go:320-326`) is raft's only
  message comparison outside tests (`raft.go:479`, `raft.go:1928`); `confchange` compares ids, not
  messages. etcd's WAL downgrade check (`server/storage/wal/version.go:59-140`) reads version
  annotations of etcd's own protos only (raftpb's were dropped with `8ece7ae`, raft's move out of
  etcd); its only `DiscardUnknown` is the gRPC gateway's JSON (`server/embed/serve.go:349`).
- **(c) Reachable only with a newer raft that sets the field.** The `ConfState` a follower
  compares comes from the leader's snapshot (`MsgSnap` -> `raft.restore`, `raft.go:1870-1928`,
  after the self-membership check and `confchange.Restore`, which ignore the field) or from its
  own storage at restart (`newRaft`, `raft.go:471-479`; etcd stores the decoded snapshot, and
  protobuf-go re-marshals unknown fields). So in a rolling upgrade an old follower panics only if
  the new leader's raft writes the new field into its tracker's `ConfState`; with proto2
  `optional` pointer fields (v3.7's generator) that happens only when the feature is in use, which
  etcd would gate on the cluster version. The downgrade path (storage written by the new version,
  read by the old) panics at every restart, under the same condition.
- **Upstream search** (`repo:etcd-io/raft Equivalent ConfState unknown`, `repo:etcd-io/raft
  "unknown fields"`): nothing.

Verdict: a genuine regression against the 2019 design (unknown fields were ignored on purpose),
but by the criterion "serious risk of a field being added, and other types dealing with unknown
fields" it is not an issue: no field is coming (one idle draft), raft's maintainers explicitly
gave up unknown-field forward compatibility in 2021, and nothing else does it. Move to
`issues/nonissues/` (with the candidate, to `nonissues/upstream/`). If #168 or any `ConfState`
field ever moves forward, revive it: the fix (`SetUnknown(nil)` on the clones, the fork branch
`fix/raft-confstate-unknown-fields-panic`) is a one-liner and restores the 2019 behaviour.
