# raft-joint-empty-transition-panic

- **Finding**: `issues/raft-joint-empty-transition-panic.md`
- **Target**: etcd-io/raft, `main` (raftpb on protobuf-go v2; v3.7.0 and 40f8be7 have the same `stepLeader` check)
- **Branch**: `raft-joint-empty-transition-panic` in `~/etcd-fixes/raft-joint-empty-transition-panic` (commit
  9e1429d86), not pushed. `issue.md` links the test at
  `https://github.com/upamanyus/etcd-raft/blob/raft-joint-empty-transition-panic/rawnode_test.go`, which resolves once
  the branch is pushed: `git -C ~/etcd-fixes/raft-joint-empty-transition-panic push origin raft-joint-empty-transition-panic`.
- **Base**: upstream `main` 638f42739b77572b5708eb0d8a776a272ade71ed (2026-10-16)
- **State**: draft
- **Upstream issue**: —
- **PR**: —

etcd-io/raft has no issue template: the issue uses etcd's bug-report sections, with "Raft version" for etcd's version
and configuration sections.

## Security

Not a security report. etcd (`main` b25719d10) proposes only v1 `raftpb.ConfChange`s (`EtcdServer.configure`,
`server/etcdserver/server.go:1749`; the only `ProposeConfChange` call), whose `AsV2()` has one change and the `Auto`
transition, so an etcd cluster never enters a joint configuration, and its apply loop rejects any
`EntryConfChangeV2` ("unknown entry type", `server.go:1930`). Client requests reach raft only as `EntryNormal`
proposals (`v3_server.go:1115`). Only an application that proposes `ConfChangeV2`s (or a peer able to send raft
messages, which is trusted) can trigger it.

## Duplicates checked (2026-10-16)

Searches on `repo:etcd-io/raft`: `"already joint"`, `wantsLeaveJoint`, `LeaveJoint transition empty`. No duplicate.
The only hit, #381 (open PR, a TLA+ specification), is unrelated.

## Verification

`TestRawNodeProposeEmptyJointConfChange` (in `rawnode_test.go`, after `TestRawNodeProposeAndConfChange`) is the
issue's example: a single-voter `RawNode` becomes leader; with `joint=true` it first proposes and applies
`ConfChangeV2{Transition: JointExplicit, Changes: [AddLearner 2]}`; then it proposes
`ConfChangeV2{Transition: JointExplicit}`, applies every committed conf change, and asserts the last entry is
`EntryNormal` (refused).

- At the base (test only): `go test . -run 'TestRawNodeProposeEmptyJointConfChange$' -v`: `joint=false` passes
  (refused, "not in joint state; refusing empty conf change"), `joint=true` panics, "config is already joint", in
  `applyConfChange` (`raft.go:1967`) from `RawNode.ApplyConfChange`.
- With the fix: the test passes; `go test . ./confchange/ ./tracker/` ok (includes the datadriven conf change
  tests in `testdata/`); `gofmt -l raft.go rawnode_test.go` empty; `go vet . ./confchange/ ./tracker/` clean
  (go1.26.9 linux/amd64).

Not run: `rafttest`, `quorum`, `raftpb`, etcd's tests, `make verify`. The `JointImplicit` variant is not in the test
(same code path: `EnterJoint()` is `ok` for any non-`Auto` transition).

## If a reviewer asks

- What changes: only a conf change with no changes and a non-`Auto` transition proposed in a joint config, now
  refused ("must transition out of joint config first") instead of accepted. v1 `ConfChange`s (always one change)
  and every other `ConfChangeV2` are checked as before; empty conf changes in a simple config are still refused.
- Alternative: `wantsLeaveJoint := cc.AsV2().LeaveJoint()` alone. In a simple config that would accept an empty
  `JointExplicit` change, which enters a joint config with no changes: a behavior change, not needed for the bug.
- Alternative: make `applyConfChange` return the error instead of panicking (its `TODO(tbg)`), or have
  `ApplyConfChange` ignore a conf change the `Changer` rejects. Not done: it changes `ApplyConfChange`'s API, and
  the entry is committed either way, so every application would have to handle it; the leader is where raft already
  refuses conf changes it cannot apply.
- Alternative: run the `Changer` on the leader's config to refuse any conf change it would reject (e.g. removing
  the last incoming voter, "removed all voters"). Broader than this bug; those other errors are for the
  application to avoid.
- `disableConfChangeValidation`: unchanged; with it set, the leader still accepts the entry and every node panics,
  as for the other refused conf changes.
