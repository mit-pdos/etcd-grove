---
upstream: none
checked: 2026-10-18
links:
blocks-proof: no
---
# raft: an empty `ConfChangeV2` with a joint transition, proposed in a joint config, panics every node that applies it

In a joint configuration, the leader accepts `ConfChangeV2{Transition: JointExplicit}` (or
`JointImplicit`) with no changes, taking it for the leave proposal; it commits, and
`ApplyConfChange` panics with "config is already joint" on every node, again at every restart.
`stepLeader` recognizes a leave by the number of changes, `applyConfChange` by `LeaveJoint()`
(the zero `ConfChangeV2`).

**Why not an issue:** reaching it takes a proposal the documentation does not describe:
`raft.proto` documents leaving a joint configuration as "proposing a ConfChangeV2 with only and
optionally the Context field populated" (the 2026-10-23 review's Plan: "the bad execution requires
violating the raft documentation's instructions"); etcd proposes only v1 `ConfChange`s and never
enters a joint configuration.

`TestRawNodeProposeEmptyJointConfChange` in
[`nonissues/raft-joint-empty-transition-panic/joint_empty_transition_test.go`](raft-joint-empty-transition-panic/joint_empty_transition_test.go)
(the fork branch's test, as a standalone file) fails at etcd-io/raft@c51f010c851e, go1.27.3:
`Error: func (assert.PanicTestFunc)(0x745720) should not panic` / `Panic value: config is already
joint`.

## Proof

no: `raft.applyConfChange.spec` and `RawNode.ApplyConfChange.spec` require the change to apply
(`ccApplyM ... = some _`, `Spec/go_etcd_io/raft/v3/raft__applyConfChange.lean`), which etcd meets (it never proposes a `ConfChangeV2`).

## Fix

**Branch**: `fix/raft-joint-empty-transition-panic` in `~/etcd-fixes/raft-joint-empty-transition-panic` (upamanyus/etcd-raft, pushed): 9659828 test, e3f1575 fix
**Base**: etcd-io/raft@638f42739b77572b5708eb0d8a776a272ade71ed

**PR draft**:

Title: raft: refuse an empty joint conf change in a joint config

In a joint config, [`stepLeader`](https://github.com/etcd-io/raft/blob/638f42739b77572b5708eb0d8a776a272ade71ed/raft.go#L1326-L1337) accepts any conf change without changes, assuming, as `wantsLeaveJoint` says, that such a conf change leaves the joint config. But [`applyConfChange`](https://github.com/etcd-io/raft/blob/638f42739b77572b5708eb0d8a776a272ade71ed/raft.go#L1957-L1967) leaves only if [`LeaveJoint`](https://github.com/etcd-io/raft/blob/638f42739b77572b5708eb0d8a776a272ade71ed/raftpb/confchange.go#L108-L114) holds (no changes, `Auto` transition); with a joint transition it enters a joint config again, which fails with "config is already joint", and panics. This PR makes the leader accept a conf change in a joint config only if `LeaveJoint` holds; outside one, empty conf changes are refused as before.

The first commit adds a test of the issue's example, which fails on `main`; the second, the fix, makes it pass.

A third commit (4ea35f1) adds a `CHANGELOG-3.8.md` entry. The one-line alternative
(`wantsLeaveJoint := cc.AsV2().LeaveJoint()`) would let an empty joint proposal outside a joint
config enter `(1)&&(1)`; the fix keeps the old refusal there.

## Notes

The argument for an issue (the upstream draft's): nothing forbids the proposal, raft already
refuses other malformed conf changes at the leader, and once committed the application cannot
skip it (`doc.go`: "ApplyConfChange must be called one way or the other"). The same class (a
committed conf change the `Changer` rejects panics every node) is
[`raft-remove-last-voter-panic`](raft-remove-last-voter-panic.md).
