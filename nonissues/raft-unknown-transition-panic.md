---
upstream: none
checked: 2026-10-16
links:
blocks-proof: no
---
# raft: a `ConfChangeV2` with an undefined `Transition` is committed, then panics every node that applies it

The leader does not check a `ConfChangeV2`'s `Transition`: one with a value other than the three
defined ones (`Auto`, `JointImplicit`, `JointExplicit`) is accepted, committed, and panics in
`ApplyConfChange` ("unknown transition", from `ConfChangeV2.EnterJoint`) on every node that
applies it, again at every restart.

**Why not an issue:** a precondition applications meet: building a `ConfChangeV2` from an
undefined enum value is not documented use; etcd proposes only v1 `ConfChange`s (`Auto`) and
rejects `EntryConfChangeV2` entries itself. At most worth documenting (the 2026-10-23 review's Plan:
"Nonissue, maybe docs").

`TestRawNodeProposeUnknownTransition` in
[`nonissues/raft-unknown-transition-panic/unknown_transition_test.go`](raft-unknown-transition-panic/unknown_transition_test.go)
fails at etcd-io/raft@c51f010c851e, go1.27.3: `Panic value: unknown transition: transition:7
changes:{type:ConfChangeAddNode node_id:2}`.

## Proof

no: `ConfChangeV2.EnterJoint.spec` (`Spec/go_etcd_io/raft/v3/raftpb/ConfChangeV2__EnterJoint.lean`)
excludes the case by a premise (`enterJointOf ... ≠ none`), as `raft.applyConfChange.spec`'s
`ccApplyM ... = some _` does; etcd meets both.

## Notes

A fix would refuse an undefined `Transition` in `stepLeader`, as it refuses other conf changes,
or have `EnterJoint` return an error.
