# raft-joint-empty-transition-panic

## Security

Not a security report. etcd (`main` b25719d10) proposes only v1 `raftpb.ConfChange`s (`EtcdServer.configure`,
`server/etcdserver/server.go:1749`; the only `ProposeConfChange` call), whose `AsV2()` has one change and the `Auto`
transition, so an etcd cluster never enters a joint configuration, and its apply loop rejects any
`EntryConfChangeV2` ("unknown entry type", `server.go:1930`). Client requests reach raft only as `EntryNormal`
proposals (`v3_server.go:1115`). Only an application that proposes `ConfChangeV2`s (or a peer able to send raft
messages, which is trusted) can trigger it.

## Candidate

- **Finding**: `issues/raft-joint-empty-transition-panic.md`
- **Target**: etcd-io/raft, `main` (raftpb on protobuf-go v2; v3.7.0 has the same `stepLeader` check)
- **Branch**: `fix/raft-joint-empty-transition-panic` in `~/etcd-fixes/raft-joint-empty-transition-panic`, three
  commits (rebuilt 2026-10-18): 9659828 adds the test, which fails there; e3f1575 is the fix; 4ea35f1 adds the
  changelog entry. Force-pushed 2026-10-19 to `upamanyus/etcd-raft` (replacing 9e1429d86); the issue's test link (`#L344-L382`) checked on GitHub: the test, doc comment to closing brace.
- **Base**: upstream `main` 638f42739b77572b5708eb0d8a776a272ade71ed (2026-10-16)
- **State**: draft, revised to the skill's 2026-10-18 standard (2026-10-18)
- **Upstream issue**: —
- **PR**: — (then replace `pull/TODO` in the changelog commit's `CHANGELOG/CHANGELOG-3.8.md` entry with its number)

etcd-io/raft has no issue template: the issue uses etcd's bug-report sections, with "Raft version" for etcd's version
and configuration sections.

## Duplicates checked (2026-10-16, again 2026-10-18)

Searches on `repo:etcd-io/raft`: `"already joint"` (0 results), `wantsLeaveJoint`, `LeaveJoint transition empty`,
`LeaveJoint transition`, `joint empty conf change panic`. No duplicate, no open PR. Hits, unrelated: #381 (open PR, a
TLA+ specification), #372 (closed: whether `EnterJoint` guarantees quorum overlap), #433 (closed: `ConfChange` passed
as a pointer).

## Other candidates

The candidates off the same `main` in etcd-io/raft each add a Bug Fixes entry to `CHANGELOG/CHANGELOG-3.8.md`, so any
two of them conflict there (checked with `git merge-tree` against `fix/raft-readindex-singleton-stale`,
`fix/raft-readindex-removed-leader` and `fix/raft-confstate-unknown-fields-panic`: the changelog is the only
conflict); whichever merges second needs a one-line rebase. `fix/raft-snapshot-during-apply-stale-confchange`, being
revised in parallel, also adds to `rawnode_test.go`/`raft_test.go` and `CHANGELOG-3.8.md`: expect the same conflict in
`CHANGELOG-3.8.md` only. The PRs are independent; `pr.md` does not mention them (no shared code).

## Why the fix works

- At the base: in a joint config with nothing pending, `stepLeader`'s `wantsLeaveJoint` is
  `len(cc.AsV2().Changes) == 0`, true for `ConfChangeV2{Transition: JointExplicit}`, so no check fails and the entry is
  appended and committed. `applyConfChange`: `LeaveJoint()` is false (the transition is not `Auto`), `EnterJoint()`
  answers `ok` for any non-`Auto` transition, and `Changer.EnterJoint` fails with "config is already joint";
  `applyConfChange` panics with that error.
- With the fix: `wantsLeaveJoint` is `cc.AsV2().LeaveJoint()`, the very test `applyConfChange` uses to leave, so a
  conf change accepted in a joint config always leaves it there; the other one is replaced by an empty `EntryNormal`
  ("must transition out of joint config first"). In a config that is not joint, the refusal keeps testing the
  number of changes (`isEmpty`), so it refuses exactly what it refused before.
- The test follows `doc.go`'s protocol: each `Ready`'s entries are appended to storage, its committed conf changes
  are applied with `ApplyConfChange` before `Advance`, and nothing else is skipped or reordered. The application's
  proposal is not a misuse that raft documents: `ConfChangeV2`'s doc (to which `ProposeConfChange` refers) says only
  that the zero `ConfChangeV2` (with an optional `Context`) leaves a joint config, raft refuses other malformed conf changes at the
  leader ("must transition out of joint config first", "not in joint state; refusing empty conf change"), and
  `doc.go` requires every committed conf change to be applied ("ApplyConfChange must be called one way or the
  other"), so the application cannot skip the entry once it is committed.

## Verification (go1.26.9 linux/amd64)

`TestRawNodeProposeEmptyJointConfChange` (in `rawnode_test.go`, after `TestRawNodeProposeAndConfChange`; the
issue's example): a single-voter `RawNode` campaigns; a local `stabilize` (as in `benchmarkRawNodeImpl`) handles
every `Ready` (append, apply each committed `EntryConfChangeV2` inside `require.NotPanics`, `Advance`); the node is
proposed `ConfChangeV2{JointExplicit, [AddLearner 2]}` and the config is checked to be joint (setup only); then it is
proposed `ConfChangeV2{JointExplicit}`. The assertion is the guarantee: each committed conf change applies without
panicking (not which entry type the leader writes instead). The earlier version (9e1429d) had a `joint=false` subtest
and asserted that the last entry was `EntryNormal`; the subtest passed on `main` and showed nothing of the bug, and
the entry type was the fix's detail, so both went.

- At the tests commit 9659828 (`go test -count=1 . -run 'TestRawNodeProposeEmptyJointConfChange$'`):

  ```
  --- FAIL: TestRawNodeProposeEmptyJointConfChange (0.00s)
          	Error Trace:	/home/ubuntu/etcd-fixes/raft-joint-empty-transition-panic/rawnode_test.go:359
          	            				/home/ubuntu/etcd-fixes/raft-joint-empty-transition-panic/rawnode_test.go:381
          	Error:      	func (assert.PanicTestFunc)(0x72a8a0) should not panic
          	            		Panic value:	config is already joint
  FAIL
  FAIL	go.etcd.io/raft/v3	0.012s
  ```

  (line 381 is the last `stabilize()`, after the empty proposal; the panic stack, trimmed here, is in
  `applyConfChange`, `raft.go:1967`, from `RawNode.ApplyConfChange`.)
- At the fix commit e3f1575: the test passes; `go test -count=1 ./...` (raft, confchange, quorum, raftpb, rafttest,
  tracker) ok, including the datadriven conf change interactions in `testdata/`; `gofmt -l .` empty; `go vet ./...`
  clean.
- The `JointImplicit` variant (the test with `JointImplicit` in the last proposal, by `go test -overlay`, 2026-10-18):
  fails the same way on `main` ("config is already joint"), passes with the fix. Not added as a test (same path).
- In a config that is not joint, `ConfChangeV2{JointExplicit}` is refused with the fix ("not in joint state;
  refusing empty conf change", by a temporary test, 2026-10-18), as on `main`.

Not run: etcd's tests, `make verify`.

## If a reviewer asks

- What changes: only a conf change with no changes and a non-`Auto` transition, proposed in a joint config, now
  refused ("must transition out of joint config first") instead of accepted. v1 `ConfChange`s (always one change)
  and every other `ConfChangeV2` are checked as before; the automatic leave (`appliedTo` proposes a nil-data
  `EntryConfChangeV2`, the zero `ConfChangeV2`) satisfies `LeaveJoint` and is accepted as before.
- Why not `wantsLeaveJoint := cc.AsV2().LeaveJoint()` alone (one line): tried (2026-10-18, by `go test -overlay`); it
  passes the test, but in a config that is not joint it accepts `ConfChangeV2{JointExplicit}` with no changes, which
  then enters the joint config `voters=(1)&&(1)` with nothing changed (run: `switched to configuration
  voters=(1)&&(1)`). A behavior change not needed for the bug; the fix keeps the old refusal (`isEmpty`).
- Why not return the error from `applyConfChange` instead of panicking (its `TODO(tbg)`), or have `ApplyConfChange`
  ignore a conf change the `Changer` rejects: it changes `ApplyConfChange`'s API, and the entry is committed either way,
  so every application would have to handle it; the leader is where raft already refuses conf changes it knows it
  cannot apply.
- Why not run the `Changer` on the leader's config and refuse any conf change it rejects (e.g. removing the last
  voter, "removed all voters"): broader than this bug; recorded separately (`issues/raft-remove-last-voter-panic.md`).
- `disableConfChangeValidation`: unchanged; with it set, the leader still accepts the entry and every node panics,
  as for the other refused conf changes.
- Docs: `ConfChangeV2`'s comment in `raftpb/raft.proto` ("Leaving the joint configuration is accomplished by proposing
  a ConfChangeV2 with only and optionally the Context field populated") and `LeaveJoint`'s ("the ConfChangeV2 is zero,
  with the possible exception of the Context field") already describe what the fix enforces; no comment in
  `stepLeader` describes the old check. Nothing to update.
- Backports: v3.7.0 has the same `stepLeader` check; not tried on a release branch. The changelog entry is in
  `CHANGELOG-3.8.md` (v3.8.0, Bug Fixes): v3.7.0 was released 2026-06-21, `main` is the 3.8 line, and raft keeps its
  changelogs on `main` only (`release-3.6` removed its copy; `release-3.7`'s is a stale alpha one). A v3.7.1 patch
  release, which raft has never made (3.6 stopped at v3.6.0; `release-3.7` has only Go bumps since v3.7.0), is the
  maintainers' call; if wanted, cherry-pick the fix commits to `release-3.7` in a separate PR and add a v3.7.1 section
  to `CHANGELOG-3.7.md` on `main`. etcd does not need it (it never proposes a `ConfChangeV2`). (Checked 2026-10-18.)
