# raft-snapshot-during-apply-stale-confchange

## Security

Not a security report. In etcd it needs a membership change (`MemberAdd`/`MemberRemove`, root when auth is on) and a
follower behind the leader's compacted log at that moment; a client with ordinary access cannot cause it. etcd
uses v1 conf changes only, so there the outcome is a wrong configuration on one member, not the joint panic.

## Candidate

- **Finding**: `issues/raft-snapshot-during-apply-stale-confchange.md`
- **Target**: etcd-io/raft, `main` (also in v3.7.0, which etcd `main` uses: `raft.go` is identical)
- **Branch**: `fix/raft-snapshot-during-apply-stale-confchange` in `~/etcd-fixes/raft-snapshot-during-apply-stale-confchange`,
  three commits: ca5cc04 adds the test, which fails there; 5b24f1e is the fix (`raft.go`, 17 lines added); da0e9bf
  adds the changelog entry. Rebuilt 2026-10-18 with a new fix (deferring the snapshot; it replaces 5acb532, which
  ignored it, and 7982f54, the same changelog commit on top of it), **not pushed**: the fork still has the earlier
  single commit c65d182 (test and the old fix together, pushed 2026-10-18). The links in `issue.md`
  (`rawnode_test.go#L718-L764`, the test from its doc comment to its closing brace; the tests commit is unchanged)
  are right only after a force-push the user approves:
  `git -C ~/etcd-fixes/raft-snapshot-during-apply-stale-confchange push --force-with-lease=fix/raft-snapshot-during-apply-stale-confchange:c65d182b85525f63906e442bcb5d2eae42c6f07b origin fix/raft-snapshot-during-apply-stale-confchange`;
  then check the line link on GitHub.
- **Base**: upstream `main` 638f42739b77572b5708eb0d8a776a272ade71ed (2026-10-16)
- **State**: draft (2026-10-18)
- **Upstream issue**: —
- **PR**: — (then replace `pull/TODO` in the changelog commit's `CHANGELOG/CHANGELOG-3.8.md` entry with its number)

etcd-io/raft has no issue template: the issue uses etcd's bug-report sections, with "Raft version" for etcd's
version and configuration sections.

Commit messages (drafts for the user to rewrite):

- `raft: test snapshot received while applying a conf change` (no body)
- `raft: defer a snapshot received while applying committed entries` — "Otherwise ApplyConfChange for one of those
  entries applies its conf change again, on top of the snapshot's configuration."
- `changelog: add entry for snapshot received while applying a conf change` (no body): Bug Fixes, "Fix wrong
  configuration or panic when a follower receives a snapshot while applying a conf change".

## Duplicates checked (2026-10-16, again 2026-10-18)

2026-10-16, `repo:etcd-io/raft`: `snapshot ApplyConfChange` (one hit, #8, closed PR "support asynchronous storage
writes", unrelated), `restore snapshot conf change applying` (none), `ApplyConfChange stale` (none).
2026-10-18: `repo:etcd-io/raft ApplyConfChange snapshot` (#8 again), `"already joint" snapshot` (0),
`restore snapshot confchange applying` (0), `ApplyConfChange twice` (0); `repo:etcd-io/etcd ApplyConfChange
snapshot restore configuration` (10, none about a snapshot stepped between a `Ready` and `ApplyConfChange`). No
duplicate, no open PR. Not searched again for the new fix (same bug). Related findings in this repository, not
reported here: `raft-advance-before-applyconfchange`, `raft-track-confchange-application`,
`raft-document-confchange-before-advance`, `raft-reportsnapshot-finish-not-noop` (found in this revision, below).

## Other candidates

Independent of every other candidate. The new fix touches `raft.go` in the `raft` struct, `appliedTo` and
`handleSnapshot`; without their changelog commits, 5b24f1e merges cleanly (`git merge-tree`, 2026-10-18) with the
fix branches of `raft-confstate-unknown-fields-panic`, `raft-joint-empty-transition-panic`,
`raft-readindex-removed-leader` and `raft-readindex-singleton-stale` (each branch's commit before its tip). All add a Bug Fixes bullet to
`CHANGELOG/CHANGELOG-3.8.md` (as do the read-index candidates), so their changelog commits conflict there:
whichever merges second needs a one-line rebase. Not mentioned in the PR (not a split).

## Why the fix works

At the base, in the test's first case: node 2 steps `MsgApp` committing "add 4" at index 1; `Ready` hands it out
(`applying` 1, `applied` 0). The `MsgSnap` at index 2 is above the commit index, so `restore` restores it:
configuration `{1,2,3}`, commit 2. `ApplyConfChange("add 4")` then applies "add 4" to `{1,2,3}`: `{1,2,3,4}`. The
resent `MsgSnap` is at or below the commit index, so it is ignored, and node 2 keeps `{1,2,3,4}`. In the joint
case the restored configuration is already joint, and `EnterJoint` panics.

With the fix, `handleSnapshot` keeps a `MsgSnap` past the commit index while `applying > applied` (committed
entries handed out and not yet applied), sends no answer, and returns. `ApplyConfChange` applies "add 4" to
`{1,2,3}`, which is right at index 1. `Advance` steps the `MsgStorageApplyResp`, whose `appliedTo` brings `applied`
to `applying` and steps the kept message again, through `Step`: same term, so `stepFollower` hands it to
`handleSnapshot`, which restores it (`{1,2,3}`, or the snapshot's joint configuration) and answers the leader with
`MsgAppResp` at the snapshot's index, as for any restored snapshot. The next `Ready` carries the snapshot. The
resent `MsgSnap` is then at the commit index and ignored.

Every path goes through `appliedTo`: `RawNode.Advance` and `node.run`'s `Advance` (the `MsgStorageApplyResp` in
`stepsOnAdvance`), and with `AsyncStorageWrites` the application's `MsgStorageApplyResp`. Points checked:

- Answer while kept: none. The leader's progress is in `StateSnapshot`, paused, so it sends only heartbeats, whose
  commit (at most `Match`) cannot move the follower's commit index past its own log; so `applying` stops growing
  and the follower ends its apply. The `MsgAppResp` sent on restore moves the leader's progress to replicate
  (`Match` reaches its first index), with no `ReportSnapshot` and no second transfer. Without `AsyncStorageWrites`
  the follower sends nothing at all until `Advance` (its heartbeat responses go out in the next `Ready`), so the
  leader cannot even probe meanwhile.
- Term checks: the kept message is stepped as received, so a message from an older term is dropped by `Step` (the
  node became candidate, or followed a newer leader). The field is not cleared in `reset`: a pre-candidate that
  hears from the same leader in the same term calls `becomeFollower` and `reset`, and clearing there would lose a
  snapshot the leader will not resend (it waits for the answer).
- A newer `MsgSnap` replaces a kept one; one message is kept at most (its `Snapshot.Data` included). The kept
  message is the caller's; raft already keeps what it is passed in `Step` (`issues/raft-step-writes-caller-message.md`).
- Nothing else of a restore is needed earlier: the follower's commit index and `Ready.Snapshot` come with the
  restore, after the apply, as for a snapshot that arrives then; a snapshot at or below the commit index is
  handled as before.
- A snapshot whose index is in the follower's log with the same term (the fast-forward case of `restore`, which
  only moves the commit index) is deferred too: harmless, and the check stays one condition.

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
needed by the new fix; it stays so that the test asserts only the guarantee (the follower ends with the snapshot's
configuration) and not whether raft restores a snapshot at once, later, or after a resend.

## Verification (go1.26.9 linux/amd64, 2026-10-18)

`TestRawNodeSnapshotDuringConfChangeApply` (`rawnode_test.go`, after `TestRawNodeRestartFromSnapshot`), two cases
in one table: v1 "add 4" with a snapshot of voters `{1,2,3}`; a `ConfChangeV2` "add 4" entering a joint
configuration (`JointExplicit`) with a snapshot in `(1 2 3 4)&&(1 2 3)`. Asserts only the guarantee: both halves of
node 2's voters equal the snapshot's.

- At the tests commit ca5cc04 (`go test -count=1 -run 'TestRawNodeSnapshotDuringConfChangeApply$' .`): fails,
  case 0 expected `[1 2 3]`, actual `[1 2 3 4]`; case 1 `panic: config is already joint`.
- At the fix commit 5b24f1e: passes; `go test -count=1 ./...` (raft, confchange, quorum, raftpb, rafttest, tracker)
  ok, also with `-race`; `gofmt -l .` empty; `go vet ./...` clean. da0e9bf differs only in the changelog.
  golangci-lint not installed, not run.
- Temporary tests, not on the branch (`go test -overlay` adding a test file; also run with the base `raft.go`, the
  old fix's and design (b)'s overlaid). New fix: all pass.
  - The branch's test without the resend: the follower ends with `[1 2 3]`, commit 2; the next `Ready` carries the
    snapshot and `MsgAppResp` at index 2. Base `[1 2 3 4]`; old fix `[1 2 3 4]`, commit 1.
  - A real leader `raft` whose log is compacted at index 2 (`{1,2,3}`), against a `RawNode` follower holding a
    `Ready` with "add 4", heartbeats only (no `ReportSnapshot`), 30 rounds: the leader sends one snapshot, the
    follower ends with `[1 2 3]`, commit 3, the leader's progress `StateReplicate match=3`. Base: `[1 2 3 4]`. Old
    fix: the follower stays at `[1 2 3 4]`, commit 1, the leader's progress `StateSnapshot ... paused` (the stall).
    With `ReportSnapshot(SnapshotFinish)` and heartbeats while the follower applies: new fix, one snapshot; old
    fix, two.
  - The same with an `AsyncStorageWrites` follower whose heartbeat responses reach the leader while it applies,
    with `ReportSnapshot(SnapshotFinish)`: new fix, the leader's probe is rejected and it sends a second snapshot
    (ignored after the restore); the follower ends with `[1 2 3]`, the leader's progress `StateReplicate`.
  - `AsyncStorageWrites` `RawNode`: the snapshot is kept (no unstable snapshot), restored on the
    `MsgStorageApplyResp`, and in the next `Ready`.
  - `Node` (`node.run`): `Step(MsgSnap)` while the application holds the `Ready`, then `ApplyConfChange`,
    `Advance`: the next `Ready` carries the snapshot, `Status` shows `[1 2 3]`, commit 2. Base: `[1 2 3 4]`.
  - A heartbeat of a newer term (from node 3) while kept: the kept message is dropped at `Advance` (voters
    `[1 2 3 4]`, commit 1, the configuration at index 1). A second `MsgSnap` at index 3 while kept replaces the
    first: restored at index 3.

Not run: etcd's tests, `make verify`. Not reproduced on a cluster or on etcd.

## etcd

etcd's raft loop (`server/etcdserver/raft.go:297-331` at etcd `main` 22cc5d9ac, raft v3.7.0) makes a follower
whose `Ready` has a conf change wait for the apply goroutine before `Advance`; meanwhile `node.run` keeps stepping
messages from the transport, `MsgSnap` included, and the apply goroutine calls `ApplyConfChange`
(`server/etcdserver/server.go:2007`, `2023`) with etcd's membership not yet replaced by the snapshot (which comes in
the next `Ready`). So etcd can reach it: a follower applying a membership change while the leader snapshots it.
etcd's membership store is then right (it restores the snapshot) while raft's configuration is not. Reasoning
from code only. With the fix, etcd's snapshot receiver has saved the snapshot's database file before stepping the
`MsgSnap`; raft restores it after the apply goroutine finishes, and the next `Ready` carries it, as for a snapshot
that arrives then. etcd's `Node` is not `AsyncStorageWrites`, so no second transfer.

## If a reviewer asks

- The kept `MsgSnap` is the caller's message, not a copy: `Step`'s contract (`raft.go:1096`, "Callers must treat
  m as immutable after passing it to Step") allows raft to keep it, and a copy would double a large snapshot's
  memory while it waits.

- Why not ignore the snapshot (the previous fix, 5acb532): `restore` returned false while `applying > applied`,
  and `handleSnapshot` answered `MsgAppResp` at the commit index. That answer leaves the leader's `Match` below its
  first index, so the leader's progress stays in `StateSnapshot` (paused) until `MsgSnapStatus`: the snapshot is
  sent again only after the leader's application calls `ReportSnapshot`, and costs a second transfer (in etcd, a
  second database transfer). `Node.ReportSnapshot`'s comment says that `SnapshotFinish` "is a no-op", so an
  application that trusts it and reports only failures would leave such a follower without a snapshot until the
  leader changes (the stall in the temporary test above). Replaced by the deferral, which needs neither.
- Alternative (b), skip stale conf changes: raft counts the conf changes it hands out and the `ApplyConfChange`
  calls, and after a restore makes the outstanding calls no-ops returning the current `ConfState`. Counting is
  wrong: `Node.ApplyConfChange`'s comment says that an application that rejects a conf change "must not" call it,
  so the count drifts, and a later restore would skip a legitimate call. A flag instead (set when a snapshot is
  restored with `applying > applied`, cleared when `applied` reaches `applying`; every call meanwhile is for an
  entry the snapshot covers) is correct under doc.go's protocol and smaller (10 lines, tried by overlay: the
  branch's test passes, `go test .` ok), restores at once and never needs a second transfer. Not taken:
  `ApplyConfChange` then returns, for an entry at index `i`, the snapshot's later `ConfState`, which the comment
  says "must be recorded in snapshots": an application that snapshots at `i` (etcd's `triggerSnapshot` after
  applying the batch) records a configuration that is not the one at `i`, and replays the conf changes after `i`
  on top of it if it restarts from that snapshot; and raft's configuration runs ahead of the application's applied
  index during the window. The deferral keeps raft's configuration and every returned `ConfState` those of the
  applied index.
- Alternative: document that `Step` must not be called between a `Ready` and its `ApplyConfChange` calls. `Node`
  does it itself (`node.run`), and doc.go puts no condition on `Node.Step`. Buffering `MsgSnap` in `node.run` while
  `advancec` is set would cover `Node` without `AsyncStorageWrites` only; the deferral is in `raft`, which every
  path reaches.
- Liveness: the snapshot is kept only while `applying > applied`, from a `Ready` handing out committed entries to
  its `Advance` (with `AsyncStorageWrites`, to the last `MsgStorageApplyResp`), which the application must reach.
  A follower the leader snapshots gets no entries from it (above), so it has finitely many entries left to apply.
- Cost: the restore waits for one apply batch. With `AsyncStorageWrites`, a `ReportSnapshot(SnapshotFinish)` while
  the follower still applies makes the leader probe, the follower reject, and the leader send a second snapshot
  (the temporary test above); the follower ignores it after the restore. Without `AsyncStorageWrites`, none.
- `ReportSnapshot`'s comment ("Calling ReportSnapshot with SnapshotFinish is a no-op"): not true at the base either
  (`MsgSnapStatus` moves the leader's progress out of `StateSnapshot`; without it, a lost answer to a restored
  snapshot stalls the follower). Recorded as `issues/raft-reportsnapshot-finish-not-noop.md`, not part of this PR:
  the new fix does not depend on it.
- Not covered: an application that calls `Advance` before `ApplyConfChange`, which doc.go's step 4 ("at any time
  after step 1") and `Node.Advance`'s comment allow. `applied` then moves at `Advance`, the snapshot is restored,
  and the later `ApplyConfChange` is applied on top of it as before. That ordering breaks raft's other conf-change
  guards too (`issues/raft-advance-before-applyconfchange.md`); this fix assumes conf changes are applied before
  `Advance`, as doc.go's example loop does. The `ApplyConfChange`-tracking prototype
  (`issues/raft-conf-lag-model/guard-fix.patch`, behind a `Config` flag) covers that ordering too.
- Comments: the field's doc says when the kept message is stepped again and that a changed term drops it; the one
  in `handleSnapshot` says why the snapshot waits (the pending `ApplyConfChange` calls), which the condition does
  not show. The log line is at Info, as `handleSnapshot`'s others. `_ = r.Step(m)` as in `rawnode.go`.
- Backports: v3.7.0 has the same `handleSnapshot` and `appliedTo`; not tried on a release branch. The changelog
  entry is in `CHANGELOG-3.8.md` (v3.8.0, Bug Fixes): `main` is the 3.8 line, and raft keeps its changelogs on
  `main` only. etcd uses v3.7.0, so the fix reaches etcd only with v3.8.0 or a v3.7.1 patch release, which raft has
  never made: the maintainers' call; if wanted, cherry-pick the fix commit to `release-3.7` in a separate PR and
  add a v3.7.1 section to `CHANGELOG-3.7.md` on `main`.

## check.py (2026-10-18)

No FAIL. WARNs, decided:

- The comments added: kept. The field's doc follows the `raft` struct's convention (every field has one) and says
  that a changed term drops the kept message, which the code in `appliedTo` does not show; the comment in
  `handleSnapshot` says why the snapshot waits.
- The issue's 260 words (aim 250): kept; it shows two cases (wrong configuration and panic). The design question
  of the previous revision is gone.
- The PR's 105 words (aim 90): kept; the approved raft example has 136.
