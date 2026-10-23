# raft-snapshot-during-apply-stale-confchange

## Security

Not a security report. In etcd it needs a membership change (`MemberAdd`/`MemberRemove`, root when auth is on) and a
follower behind the leader's compacted log at that moment; a client with ordinary access cannot cause it. etcd
uses v1 conf changes only, so there the outcome is a wrong configuration on one member, not the joint panic.

## Candidate

- **Finding**: `issues/raft-snapshot-during-apply-stale-confchange.md`
- **Target**: etcd-io/raft, `main` (also in v3.7.0, which etcd `main` uses: `raft.go` and `rawnode.go` are identical
  in the lines changed)
- **Branch**: `fix/raft-snapshot-during-apply-stale-confchange` in `~/etcd-fixes/raft-snapshot-during-apply-stale-confchange`,
  two commits: 43af980 adds the test, which fails there; 9dc2d50 is the fix (`raft.go` 22 lines added, 18
  removed; `rawnode.go` 35 added, 17 removed; and the tests that relied on `restore` switching the configuration:
  `raft_test.go`, `raft_snap_test.go`, eight `testdata/` files). 2026-10-23: the changelog commit (4a0c81d) dropped
  (a bug fix the maintainers would backport gets none, the etcd-io/raft#536 review) and `storageAppendHeld`'s doc
  comment shortened to the one of `raft-async-snapshot-during-apply-divergence`, split off (below); the fix was
  a896f58; the old head is kept as `backup/raft-snapshot-during-apply-stale-confchange-v4-changelog` (4a0c81d).
  Rebuilt 2026-10-21 with a fourth fix, option A: switch to the snapshot's configuration when the
  snapshot is applied (`appliedSnap`) instead of when it is restored, and with `AsyncStorageWrites` hold the append
  thread's work while a snapshot waits for older entries (the user's choice over the third fix, which kept a copy
  of the pre-snapshot configuration; below). Earlier fixes kept as local branches:
  `backup/raft-snapshot-during-apply-stale-confchange-v3-keepconf` (9f77761: a016d92, b556234, 9f77761, the copy),
  `backup/raft-snapshot-during-apply-stale-confchange-v2-defer` (48dafe8, the deferral) and
  `backup/raft-snapshot-during-apply-stale-confchange-v1` (da0e9bf, the first push's head).
- **Base**: upstream `main` 1931ff5beacc1e2539003c0c70f096285f04c425 (2026-10-19, the merge of #536; still `main`
  on 2026-10-23, so not rebuilt). The test's lines are `rawnode_test.go#L718-L851`; the PR's permalinks are at
  1931ff5. Pushed before: the fork still has `da0e9bf` (the deferral, on the old base, checked with `git ls-remote
  origin` 2026-10-23); replace it, once the user approves, with
  `git -C ~/etcd-fixes/raft-snapshot-during-apply-stale-confchange push --force-with-lease=fix/raft-snapshot-during-apply-stale-confchange:da0e9bf origin fix/raft-snapshot-during-apply-stale-confchange`
- **State**: draft (2026-10-23)
- **Upstream issue**: —
- **PR**: —

etcd-io/raft has no issue template: the issue uses etcd's bug-report sections, with "Raft version" for etcd's
version and configuration sections.

Commit messages (drafts for the user to rewrite):

- `raft: test snapshot received while applying a conf change` (no body)
- `raft: switch to a snapshot's configuration when it is applied` — "Conf changes applied after a snapshot was
  restored applied on top of its configuration, though the snapshot already included them."
- No changelog commit (dropped 2026-10-23; it was `changelog: add entry for snapshot received while applying a
  conf change`, on the backup branch, if a reviewer asks for one).

## Duplicates checked (2026-10-16, again 2026-10-18)

2026-10-16, `repo:etcd-io/raft`: `snapshot ApplyConfChange` (one hit, #8, closed PR "support asynchronous storage
writes", unrelated), `restore snapshot conf change applying` (none), `ApplyConfChange stale` (none).
2026-10-18: `repo:etcd-io/raft ApplyConfChange snapshot` (#8 again), `"already joint" snapshot` (0),
`restore snapshot confchange applying` (0), `ApplyConfChange twice` (0); `repo:etcd-io/etcd ApplyConfChange
snapshot restore configuration` (10, none about a snapshot stepped between a `Ready` and `ApplyConfChange`). No
duplicate, no open PR. Not searched again for the new fix (same bug). Related findings in this repository, not
reported here: `raft-advance-before-applyconfchange`, `raft-track-confchange-application`,
`raft-document-confchange-before-advance`, `raft-reportsnapshot-finish-not-noop` (found in this revision, below).

2026-10-23: `repo:etcd-io/raft` `snapshot ApplyConfChange` (#8), `"already joint"` (0), `snapshot ConfState
updated:>=2026-10-18` (0), `MsgSnap "conf change"` (0); `repo:etcd-io/etcd "config is already joint"` (0); every
etcd-io/raft issue and PR created or updated since 2026-10-18 (version bumps, the read-index fixes #533-#536) and
the 30 most recently updated open PRs: no duplicate, no open PR.

2026-10-21, for the `AsyncStorageWrites` half (`issues/raft-async-snapshot-during-apply-divergence.md`):
`repo:etcd-io/raft` `AsyncStorageWrites snapshot` (#8, #110), `MsgStorageAppend snapshot` (#8, #161), `async storage
writes snapshot` (#8, #37), `LocalApplyThread` (#8); and the review threads of #8 and of etcd-io/etcd#14627 (where
#8 started): none about a snapshot handed out while committed entries are being applied.

## Other candidates

The fix touches `raft.go` (`appliedSnap`, `restore`) and `rawnode.go` (`readyWithoutAccept`, `acceptReady`,
`HasReady`, a new `storageAppendHeld`). a896f58 (whose code 9dc2d50 keeps) merged cleanly
(`git merge-tree`, 2026-10-21) with the code commits of `raft-confstate-unknown-fields-panic` (71ca492) and
`raft-joint-empty-transition-panic` (e3f1575) (each branch's commit before its changelog tip; both are still on
638f42739) and with the tips of `raft-advance-before-applyconfchange` (fd30b41),
`raft-memorystorage-initialstate-unlocked` (15190e3) and `raft-readindex-singleton-stale` (3d0bd8a); each of the
first four merges builds, vets and passes `go test ./...`. Now that this branch has no changelog commit, only those
siblings' changelog commits conflict, with `main` itself. Not mentioned in the PR (not a split). 2026-10-23: 9dc2d50
merges cleanly with fd30b41 (`git merge-tree`).

**`raft-async-snapshot-during-apply-divergence`** (split off 2026-10-23, `issues/upstream/raft-async-snapshot-during-apply-divergence/`,
branch `fix/raft-async-snapshot-during-apply-divergence`, fix b60b90c): the `AsyncStorageWrites` half (the hold)
also fixes the state machine applying older entries after a snapshot that includes them, a distinct trigger (no
conf change), symptom and workaround, so by the split rule it is an issue and PR of its own. Until 2026-10-21's
review it was kept here because this fix needs the hold (with `AsyncStorageWrites`, without it, `appliedSnap` can
switch the configuration before the stale `ApplyConfChange` calls: the two async subtests fail). Both branches
therefore carry the identical `rawnode.go` change (same hunks, same doc comment, `git diff b60b90c 9dc2d50 --
rawnode.go` empty), so they merge cleanly in either order (`git merge-tree`; the merged tree vets and passes `go test
./...`, both new tests included), and neither depends on the other: that fix alone leaves this test failing (three
of four subtests), this fix alone passes that test. Each PR ends with a note on the overlap.

## Why the fix works

At the base, in the test's first case: node 2 steps `MsgApp` committing "add 4" at index 1; `Ready` hands it out
(`applying` 1, `applied` 0). The `MsgSnap` at index 2 is above the commit index, so `restore` restores it and
switches to its configuration `{1,2,3}`, commit 2. `ApplyConfChange("add 4")` then applies "add 4" to `{1,2,3}`:
`{1,2,3,4}`. The next `Ready` carries the snapshot, which the application applies, but nothing re-installs its
configuration, and the resent `MsgSnap` is at or below the commit index, so it is ignored: node 2 keeps
`{1,2,3,4}`. In the joint case the restored configuration is already joint, and `EnterJoint` panics.

With the fix, `restore` restores the log as before (commit 2, the snapshot in the unstable log, `MsgAppResp` at
index 2 to the leader) but leaves the configuration `{1,2,3}`. `ApplyConfChange("add 4")` applies to it:
`{1,2,3,4}`, the configuration at index 1, which is also what it returns. `Advance`; the next `Ready` carries the
snapshot; the application applies it and calls `Advance`, which steps the `MsgStorageAppendResp` carrying it:
`appliedSnap` now switches to the snapshot's configuration, `{1,2,3}`. In the joint case `EnterJoint` applies to
`{1,2,3}` and `appliedSnap` installs the snapshot's joint configuration.

- The invariant: the configuration is the one at the applied index, which is how conf change entries already
  work (they take effect when applied). A snapshot is now one more thing that is applied in log order.
- Without `AsyncStorageWrites`, the order is forced: `RawNode` refuses a second `Ready` before `Advance`, so the
  snapshot's `Ready` (and its acknowledgement) comes after the `Advance` of the entries handed out before it, and
  doc.go's protocol puts their `ApplyConfChange` calls before that `Advance`.
- With `AsyncStorageWrites`, the snapshot goes to the append thread and the older entries to the apply thread,
  "processed in any order" (`Config.AsyncStorageWrites`), so the snapshot could be acknowledged first (the async
  subtests fail without the hold). `storageAppendHeld`: while an unstable snapshot is not yet handed out and
  `applying > applied`, `RawNode` hands nothing to the append thread: not the snapshot, not the entries after it,
  not a `HardState` (its commit index is the snapshot's), not `msgsAfterAppend` (the `MsgAppResp` acknowledging
  the snapshot must wait until it is durable). `HasReady` ignores them meanwhile, and `acceptReady` keeps
  `msgsAfterAppend` and does not mark the unstable log in progress. The apply thread's response for the older
  entries makes `applied == applying`, and the next `Ready` hands everything out. The condition can only become
  true at a restore: no committed entries are handed out while a snapshot is pending
  (`hasNextOrInProgressSnapshot`).
- Nothing else reads a follower's configuration for a decision in the window between the restore and
  `appliedSnap`: the follower cannot campaign (`promotable` is false while a snapshot is pending, `hup` checks it),
  so it never counts votes or commits; granting a vote does not read the configuration; the window ends at the
  acknowledgement, which the application must deliver.
- Without a snapshot restored, nothing changes: the configuration switch happens at the same acknowledgement as
  `appliedTo`, and the hold's condition is false.

## Why the test shows the bug, not a misuse

doc.go's protocol: the application persists the `Ready`'s entries, applies its committed entries, calling
`ApplyConfChange` for each conf change, then calls `Advance`; it passes received messages to `Step` with no
condition. `node.run` steps `recvc` messages while it waits for `Advance` (`node.go:394-399`, `advancec` set at
`node.go:435-446`), and `RawNode` has no rule against `Step` between `Ready` and `Advance`. The test does exactly
that: `Ready`, persist the entries, `Step(MsgSnap)`, `ApplyConfChange`, `Advance`. The gap (a snapshot stepped
while the application applies) is the bug's trigger, not an avoidable one: it is the time the application takes
to persist and apply. `ApplyConfChange` is called before `Advance`, right after the entry is handed out.

The leader's messages are built by hand (a `MsgApp` committing index 1, then a `MsgSnap` at index 2, each of a
kind a leader sends); `newNetwork`'s peers are bare `raft`s with no `Ready`/apply cycle, so the test drives a
`RawNode`, as `rawnode_test.go`'s tests do. In a cluster the snapshot needs a follower behind the leader's
compaction point while it is still applying an older batch. The test's second `Step(snap)` (a resend) is not
needed by the fix; it stays so that the test asserts only the guarantee (the follower ends with the snapshot's
configuration, `ApplyConfChange` returns the configuration at the entry's index) and not when raft restores the
snapshot. The application processes every `Ready` until none is left, so the test does not depend on when raft
switches the configuration either. The async subtests run the append thread ahead of the apply thread, the order
doc.go allows that exposes the race; the apply thread calls `ApplyConfChange` before delivering its response, as
doc.go's apply thread does.

## Verification (go1.26.9 linux/amd64, 2026-10-21; rerun 2026-10-23)

2026-10-23, after dropping the changelog commit and amending the comment: at 43af980 the test fails as below
(`0/async=false`, `0/async=true` `expected: []uint64{0x1, 0x2, 0x3}`, `actual  : []uint64{0x1, 0x2, 0x3, 0x4}`;
`1/async=false` `panic: config is already joint [recovered, repanicked]`); at 9dc2d50 it passes, `go test -count=1
./...` ok, also with `-race`; `gofmt -l .` empty; `go vet ./...` clean.


`TestRawNodeSnapshotDuringConfChangeApply` (`rawnode_test.go`, after `TestRawNodeRestartFromSnapshot`), two cases
times two modes: v1 "add 4" with a snapshot of voters `{1,2,3}`; a `ConfChangeV2` "add 4" entering a joint
configuration (`JointExplicit`) with a snapshot in `(1 2 3 4)&&(1 2 3)`; each without and with
`AsyncStorageWrites`. Asserts the guarantee: `ApplyConfChange` returns the configuration at index 1, and both
halves of node 2's voters equal the snapshot's.

- At the tests commit 43af980 (`go test -count=1 -run 'TestRawNodeSnapshotDuringConfChangeApply$' .`): fails,
  `0/async=false` and `0/async=true` `expected: []uint64{0x1, 0x2, 0x3}`, `actual: []uint64{0x1, 0x2, 0x3, 0x4}`;
  `1/async=false` `panic: config is already joint` (which ends the run).
- At the fix commit a896f58 (9dc2d50 differs only in a comment): passes (all four); `go test -count=1 ./...`
  (raft, confchange, quorum, raftpb, rafttest, tracker) ok, also with `-race`; `gofmt -l .` empty; `go vet ./...`
  clean. golangci-lint not installed, not run.
- Without the hold (`storageAppendHeld` returning false): the two `async=true` subtests fail, the two others pass.
- The tests the fix changes: `TestRestore`, `TestRestoreWithLearner`, `TestRestoreWithVotersOutgoing` and
  `TestRestoreLearnerPromotion` now check that the configuration is unchanged after `restore` (where the old
  assertion was on it) and is the snapshot's after the snapshot is applied (`applyRestoredSnapshot`, a helper doing
  what `TestLearnerReceiveSnapshot` already does inline: `ApplySnapshot` to storage, `appliedSnap`);
  `TestSendingSnapshotSetPendingSnapshot`, `TestProvideSnap` and `TestIgnoreProvidingSnap` use `restore` to set up a
  leader with a compacted log and now apply the snapshot too (they panicked on `Progress[2]`, peer 2 coming only
  from the snapshot). `TestInteraction` (`-rewrite`): eight files, nine "switched to configuration" lines, each
  moved from the step delivering the `MsgSnap` to the step applying the snapshot; no other line changes, messages
  included.
- Temporary tests, not on the branch (`go test -overlay`, in the job's scratch directory), at the fix:
  - `RawNode`: right after the restore the configuration is still `[1 2 3]`; the stale "add 4" returns
    `[1 2 3 4]` and makes the configuration `[1 2 3 4]` (the configuration at index 1); after the snapshot's
    `Ready`, `[1 2 3]`; an "add 4" at index 3 then makes it `[1 2 3 4]`.
  - `AsyncStorageWrites` `RawNode`, the append thread run as soon as it has work: after the `MsgSnap` nothing is
    handed to the append thread and `applied` stays 0; a `MsgApp` at index 3, a heartbeat and a probe at index 2
    arriving meanwhile are answered with no rejection (only the heartbeat response goes out: the `MsgAppResp`s are
    held); the apply thread's "add 4" returns `[1 2 3 4]`; its response releases the snapshot: a state machine
    appending entries ends with "ab" (the snapshot's), not "aba"; the held `MsgAppResp`s (up to index 3) go out;
    the configuration is `[1 2 3]`; entry 3 is handed out after the snapshot and its "add 4" gives `[1 2 3 4]`.
  - `Node`: `Step(MsgSnap)` while the application holds the `Ready`; `ApplyConfChange` returns `[1 2 3 4]`; after
    `Advance` the next `Ready` carries the snapshot; `Status` then shows `[1 2 3]`, commit 2.
  - `Node`, a stale "remove 2" at node 2 with a snapshot that keeps 2: node 2 ends with `[1 2 3]`, but `Propose` at
    node 2 blocks (`context deadline exceeded` after 200 ms): applying "remove 2" to the configuration in use made
    `node.run` stop taking proposals until the leader changes (below). At the base: `[1 3]` (the bug) and
    `Propose` blocks; with the third fix (the copy): `[1 2 3]` and `Propose` succeeds.
- Not re-run for this fix: the resend count against a real leader (the third fix's table: 1 `MsgSnap` in each
  variant; the temporary test is gone). Without `AsyncStorageWrites` the follower's messages are those of the base
  (the interaction tests' traces are unchanged but for the log lines; `restore` and its `MsgAppResp` are
  untouched). With it, the follower's log holds the snapshot from the restore on, so a probe at or after it is
  accepted, not rejected (checked above), and only a rejection below the leader's first index makes the leader
  send another snapshot.

Not run: etcd's tests, `make verify`. Not reproduced on a cluster or on etcd.

## etcd

etcd's raft loop (`server/etcdserver/raft.go:289-331` at etcd `main` 7ff040cb8, raft v3.7.0) makes a follower
whose `Ready` has a conf change wait for the apply goroutine before sending that `Ready`'s messages and calling
`Advance`; meanwhile `node.run` keeps stepping messages from the transport, `MsgSnap` included (rafthttp's
snapshot handler, `api/rafthttp/http.go:307-330`, saves the database file, then steps the message, then answers the POST, after which the
leader's sender calls `ReportSnapshot(SnapshotFinish)`), and the apply goroutine calls `ApplyConfChange`
(`server/etcdserver/server.go:2007`, `2023`) with etcd's membership not yet replaced by the snapshot (which comes in
the next `Ready`). So etcd can reach it: a follower applying a membership change while the leader snapshots it.
etcd's membership store is then right (it restores the snapshot) while raft's configuration is not. Reasoning
from code only. With the fix, raft restores the snapshot at once, as at the base, the stale call applies to the configuration
in use and returns the configuration at its index, which etcd stores in `ep.confState` and in its local snapshots
(below), and raft's configuration becomes the snapshot's when etcd applies it (`applySnapshot`, then `Advance`).
etcd does not enable `AsyncStorageWrites`.

## If a reviewer asks

Candidate layers and fixes, and why this one:

- Document that `Step` must not be called between a `Ready` and its `ApplyConfChange` calls: `Node` does it
  itself (`node.run`), and doc.go puts no condition on `Node.Step`. Buffering `MsgSnap` in `node.run` while
  `advancec` is set covers `Node` without `AsyncStorageWrites` only.
- Ignore the snapshot (the first fix, 5acb532): `restore` returned false while `applying > applied`, and
  `handleSnapshot` answered `MsgAppResp` at the commit index. That answer leaves the leader's `Match` below its
  first index, so its progress stays in `StateSnapshot` (paused) until `MsgSnapStatus`: the snapshot is sent again
  only after the leader's application calls `ReportSnapshot`, a second transfer every time, and never if the
  application trusts `ReportSnapshot`'s comment that `SnapshotFinish` "is a no-op" (the stall,
  `issues/raft-reportsnapshot-finish-not-noop.md`).
- Defer the snapshot (the second fix, bfbb745, on `backup/...-v2-defer`): keep a `MsgSnap` received while
  `applying > applied` and step it again when `appliedTo` brings `applied` to `applying`. Correct, 17 lines, but
  measured (the third fix's verification): the leader sends the snapshot a second time when, after
  `ReportSnapshot(SnapshotFinish)`, it gets any answer from the follower while the follower still defers (it
  probes past the snapshot, the follower rejects, its log is compacted), and when the term changes while the
  snapshot waits. In etcd each is a full database transfer.
- Skip stale calls by counting (raft counts the conf changes it hands out and the `ApplyConfChange` calls): wrong,
  an application that rejects a change "must not" call `ApplyConfChange`, so the count drifts.
- Skip stale calls by a flag (meanwhile `ApplyConfChange` changes nothing and returns the current `ConfState`):
  rejected: a call for entry `i` returns the snapshot's later `ConfState`, and `ApplyConfChange`'s comment says the
  result "must be recorded in snapshots". Real in etcd (`server.go:978-999`, `2023`, `2102`): `applyConfChange`
  stores it in `ep.confState`, which `CreateSnapshot(ep.appliedi, ep.confState)` can write into a snapshot at `i`
  before the leader's snapshot is saved. raft's own `rafttest` harness records each returned `ConfState` as the
  snapshot at that entry's index (`processApply`). Reasoning from code; not run on etcd.
- Track which entry each `ApplyConfChange` is for (`issues/raft-conf-lag-model/guard-fix.patch`, behind a
  `Config` flag): covers more (an `Advance` before `ApplyConfChange`), but a new option and API surface.
- Keep a copy of the pre-snapshot configuration (the third fix, b556234, on `backup/...-v3-keepconf`): `restore`
  switches as before but keeps the configuration it replaced, with the index of the last entry handed out; the
  stale calls change the copy and return its `ConfState`; the copy goes at that entry's acknowledgement; with
  `AsyncStorageWrites`, no newer entries meanwhile. Correct, and it leaves raft's configuration exactly as at the
  base, but it adds two fields and a second configuration that `ApplyConfChange` may change, and it leaves the
  async state-machine order (`raft-async-snapshot-during-apply-divergence`) as it is.
- This fix (option A): the configuration changes when the snapshot is applied. No new state in `raft`; the
  snapshot is restored at once, so nothing is sent twice; each `ApplyConfChange` returns what it returns at the
  base without the snapshot; it does not count calls. It restores an invariant raft already relies on for conf
  change entries (the configuration is the one at the applied index), where `restore` was the exception. The
  async hold is the one extra piece, and it also makes a snapshot apply after the entries before it.

Other questions:

- Is it safe for a follower to keep the old configuration between the restore and `appliedSnap`? The follower
  makes no decision with it then: it cannot campaign (`promotable` is false while a snapshot is pending), so it
  never counts votes, commits or tracks replication; granting a vote does not read the configuration. A follower
  with committed but unapplied conf changes is in the same position at the base, and raft guards it the same way
  (`hup` refuses to campaign while `hasUnappliedConfChanges`). A crash in the window restarts from storage: before
  the snapshot is saved, from the old state (the leader sends it again); after, from the snapshot's `ConfState`
  (`Storage.InitialState`), which is what `appliedSnap` would have installed.
- What changes in the window (liveness and observability, not safety): `Status().Config` and `WithProgress` show
  the old configuration until the snapshot is applied (at the base the snapshot's, next to an `Applied` below
  it); `RawNode.Step` and `node.run` drop responses from peers not in it, which for a follower matters only for a
  `MsgReadIndexResp` from a leader that joined later (the read is retried, as with apply lag at the base); a stale
  conf change that removes the node itself, from a snapshot that re-adds it, makes `node.run` stop taking
  proposals until the leader changes (`node.go:403-427`, "not very sound and likely has bugs"), as a
  remove-then-re-add without a snapshot does at the base (measured above; the third fix avoided it). etcd reads
  `Status().Lead` and, on the leader only, `Status().Progress`.
- Cost of the hold (only with `AsyncStorageWrites`, only while a snapshot waits for older entries): the follower
  persists nothing meanwhile, so its `MsgAppResp`s and vote responses wait for the older entries' application;
  heartbeat responses do not wait. The wait ends at the apply thread's response, which the application must
  deliver.
- Not covered: an application that calls `Advance` before `ApplyConfChange`, which doc.go's step 4 ("at any time
  after step 1") and `Node.Advance`'s comment allow. The snapshot's `Ready` can then be applied before the late
  `ApplyConfChange`, which applies on top of the snapshot's configuration as before. That ordering breaks raft's
  other conf-change guards too (`issues/raft-advance-before-applyconfchange.md`); this fix assumes conf changes
  are applied before `Advance`, as doc.go's example loop does (and etcd, for a follower's `Ready` with a conf
  change).
- Comments: one in `appliedSnap` (why the switch waits for the snapshot to be applied), the doc of
  `storageAppendHeld` (why nothing goes to the append thread, and why it never holds without
  `AsyncStorageWrites`); `restore`'s doc comment says the configuration is restored in `appliedSnap`.
- `ReportSnapshot`'s comment ("Calling ReportSnapshot with SnapshotFinish is a no-op"): not true at the base
  (`issues/raft-reportsnapshot-finish-not-noop.md`), not part of this PR; the fix does not depend on it.
- Backports: v3.7.0 has the same `restore`, `appliedSnap` and `RawNode` code; not tried on a release branch. No
  changelog entry (a bug fix to backport; add one in `CHANGELOG-3.8.md` if a reviewer asks). etcd uses v3.7.0, so
  the fix reaches etcd only with v3.8.0 or a v3.7.1 patch release, which raft has never made: the maintainers'
  call; if wanted, cherry-pick the fix commit to `release-3.7` in a separate PR.
- An application that calls `Advance` before `ApplyConfChange` (not covered, above): `raft-advance-before-applyconfchange`'s
  documentation PR makes that order a misuse, so the case this fix leaves out is then outside the contract.

## check.py (2026-10-23)

No FAIL. WARNs, decided:

- The comments added: kept. The one in `appliedSnap` says why the switch waits for the snapshot to be applied,
  and `storageAppendHeld`'s doc says why nothing goes to the append thread and why it never holds without
  `AsyncStorageWrites`, neither of which the code shows; `restore`'s doc comment is updated to what it now does;
  "This should never happen ..." moved with the code from `restore`.
- The issue's 272 words (aim 250): kept; it shows two cases (wrong configuration and panic) and both modes.
- The PR's words (aim 90): kept; the approved raft example has 136, and the change needs both halves (the
  switch in `appliedSnap`, the hold with `AsyncStorageWrites`) plus the overlap note.
