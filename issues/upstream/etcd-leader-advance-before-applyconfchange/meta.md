# etcd-leader-advance-before-applyconfchange

## Security

Not a security report: it needs membership changes (`MemberAdd`/`MemberRemove`, root when auth is on), a slow apply
loop on the leader and a partition; a client with ordinary access cannot cause it. No wrong result has been shown
on etcd.

## Candidate

- **Finding**: `issues/etcd-leader-advance-before-applyconfchange.md` (part of the finding
  `raft-advance-before-applyconfchange`; the raft side is `issues/upstream/raft-advance-before-applyconfchange/`)
- **Target**: etcd-io/etcd, `main`
- **Branch**: `fix/etcd-leader-advance-before-applyconfchange` in `~/etcd-fixes/etcd-leader-advance-before-applyconfchange`,
  two commits: 06f2a0238 (the test), 18ed639bc (the fix,
  `server/etcdserver/raft.go`, 11 lines added).
- **Base**: upstream `main` 7ff040cb84c9944d0c38a9f0dc9f12ed9c58223b (2026-10-20)
- **State**: draft, on hold (2026-10-21). File only after the raft PR (documenting that a `Ready`'s conf changes
  must be applied before `Advance`) is accepted: the issue's expectation cites that rule in `Node.Advance`, which
  does not exist until then. The evidence is a contract violation shown by a unit test; no wrong result on an etcd
  cluster was reproduced (the ranking: "claiming etcd is affected needs more evidence"), and the issue does not claim
  one. The user decides whether that is enough to file.
- **Investigation 2026-10-23** (is a bad execution actually possible?): yes in principle, and no etcd check prevents
  it — see the finding's 2026-10-23 note. Re-verified at upstream `main` 3aaab3479 / raft v3.7.0: the leader branch
  still does not wait (contract test `StateLeader` fails at HEAD); `DisableConfChangeValidation` is off in
  `raftConfig` (so the defeated `pendingConfIndex > applied` guard is the only propose-time protection); and
  `ValidateConfigurationChange` validates each change against the sequentially-applied store, so it does not turn the
  overlapping change into a no-op. Still no end-to-end cluster reproduction (window sub-ms; needs a stalled leader
  apply + two concurrent conf-change clients + a partition; add-member route also needs node 4 to catch up via node
  3). Does not change the "on hold" decision.
- **Upstream issue**: —
- **PR**: —

Push: `git -C ~/etcd-fixes/etcd-leader-advance-before-applyconfchange push origin fix/etcd-leader-advance-before-applyconfchange`;
then check the issue's link `#L214-L268` on GitHub.

Commit messages (drafts for the user to rewrite):

- `etcdserver: test that a leader waits for conf changes to be applied` (no body)
- `etcdserver: apply conf changes before Advance on the leader too` — "Otherwise the leader's raft accepts a second
  conf change while it still uses the configuration before the first."

## Duplicates checked (2026-10-21)

With the raft candidate's searches: `repo:etcd-io/etcd Advance ApplyConfChange leader` (issues: #20009, #13418,
#12098, #7985, #4203; PRs: #14627, #1874, #1586; none about the leader advancing before applying a conf change;
#4203 is the 2016 documentation question). The finding's front matter adds etcd-io/raft#354 (related, not this
bug). No duplicate, no open PR.

## Other candidates

Depends on the raft candidate `raft-advance-before-applyconfchange` for its justification (not a split: another
repository; the raft PR changes documentation only, so nothing to merge together). Independent of every other etcd
candidate; the change is in `raftNode.start`'s leader branch only.

## Why the fix works

At the base, `raftNode.start` (`server/etcdserver/raft.go:289-336`) hands a `Ready`'s committed entries to the apply
loop, then on a follower or candidate, if they include a conf change, sends `notifyc` a second time, which blocks
until `applyAll` has received the first one after `applyEntries` (`server.go:978-989`), i.e. after
`applyConfChange` has called `s.r.ApplyConfChange`. On the leader it sends once and calls `r.Advance()` at once.
raft v3.7.0's `Advance` steps the `MsgStorageApplyResp` that moves the applied index; its check before accepting a
conf change proposal is `pendingConfIndex > applied` (`raft.go:1326`), false from then on, while raft's
configuration changes only at `ApplyConfChange`. The fix adds the follower's second send to the leader branch, so
`Advance` comes after the apply loop has applied the batch.

The test is `TestConfigChangeBlocksApply` (the existing test of the follower's wait) run for `StateLeader` too, as
subtests in a loop over the two states (the body re-indented, otherwise unchanged but for the state; `git diff -w`
shows 5 lines): a
`Ready` from a leader with a conf change entry; the raft loop must not hand out the next batch until the first
batch's apply is finished. At the base the `StateLeader` case fails ("raft routine should block waiting for
toApply"); with the fix both pass.

## Why the test shows the bug, not a misuse

The test's `Ready` has the shape a leader's has (`SoftState` leader, a committed `EntryConfChange`); the fake node
and the harness are the existing test's. The assertion is the existing test's guarantee, now for the leader.

What is not shown: a wrong result on etcd. The sequence on raft (`TestNodeAdvanceBeforeApplyConfChange`, the raft
candidate) needs, in etcd: a leader whose apply loop is still applying a `MemberAdd`/`MemberRemove` while a second
membership change from another client reaches raft, then a partition. etcd's own checks before proposing
(`mayAddMember`/`mayRemoveMember`) read the applied membership and do not serialize two clients' changes, and
`configure` waits only for its own change (code reading). An integration test would need the apply loop held
(the `beforeApplyOneConfChange` failpoint needs a gofail build) and pairwise partitions; not attempted.

## Verification (go1.27.1 linux/amd64, 2026-10-21)

- At the test commit 06f2a0238 (`cd server && go test -count=1 -run 'TestConfigChangeBlocksApply$' ./etcdserver/`):
  `--- FAIL: TestConfigChangeBlocksApply/StateLeader`, "raft_test.go:251: unexpected execution: raft routine should
  block waiting for toApply"; `StateFollower` passes.
- At the fix commit 18ed639bc: both cases pass; `go test -count=1 ./etcdserver/...` ok; `go test -race -count=1
  ./etcdserver/` ok; `gofmt -l` empty on the two files; `go vet ./etcdserver/` clean.
- The integration run below was at the earlier fix commit 94aafb90f, whose `raft.go` is the same as 18ed639bc's
  (only the test was re-indented and the messages rewritten); not rerun.
- Integration (`cd tests && go test -count=1 -run 'Member|TestCluster|TestIssue|TestRestartMember|TestLearner|TestAddMember|TestRemove|Rotation|TestSpeedyTerminate|TestKVPutStoppedServerAndClose' ./integration/ ./integration/clientv3/`):
  ok (31 tests pass, 2 skipped), including `TestAddMemberAfterClusterFullRotation`, `TestRemoveMember`,
  `TestNetworkPartition*`, `TestIssue2746`, `TestIssue3699`.
- Not run: `make verify`, e2e and robustness tests.

## If a reviewer asks

- What the leader waits on, and shutdown: the second send on `notifyc` (capacity 1) completes once `applyAll` has
  received the first, after `applyEntries` has returned (`server.go:978-989`; a leader's `Ready` carries no
  snapshot, so `applySnapshot` does not take it first). The apply path does not wait on the raft loop: its
  `ApplyConfChange` goes to raft's own node goroutine, `configure`'s wait on `raftAdvancedC` is in the proposer's
  goroutine, and followers already run the same apply code while their raft loop waits. If the apply goroutine stops
  (`sched.Stop` in `run`'s shutdown), `s.r.stop()` follows and the wait's `case <-r.stopped` returns, as in the
  follower's wait.
- Hot path: the wait runs only for a `Ready` whose committed entries include a conf change (`confChanged`); every
  other leader batch is unchanged.

- Cost: on a batch with a membership change the leader's raft loop waits for its apply loop before `Advance`, so
  for that batch the leader hands out no new `Ready` (no heartbeats, no appends) until the batch is applied, as
  followers already do. Membership changes are rare; a long batch apply could delay heartbeats past the election
  timeout once.
- Why not wait only when a second membership change is pending: the raft loop does not know; raft accepts it
  inside `Advance`'s window, whoever proposed it.
- Why not set raft's `DisableConfChangeValidation`: it removes the check altogether.
- If raft adopts conf change tracking instead (alternative (b) of the raft candidate, opt-in), etcd could set it, but
  would then have to call `ApplyConfChange` with a zero `NodeId` for the conf entries it replays and skips after a
  restart (`server.go:2018-2024`), or those members could never campaign again.
- A second route with the same window: a leader that steps down after `Advance` and before its apply loop applies
  the conf change campaigns as a follower with that change unapplied (the follower-path wait does not cover a
  `Ready` handled as leader). Covered by the same fix.
- Duplicate code: the wait is the follower's six lines; sharing them would move the follower's wait relative to its
  message send, which is out of scope.

## check.py (2026-10-21)

No FAIL. WARNs, decided:

- The added comment in `raft.go`: kept; it says why the leader waits (raft's check reads the applied index), which
  the code does not show.
- The PR's 102 words (aim 90): kept; the approved raft example has 136.
