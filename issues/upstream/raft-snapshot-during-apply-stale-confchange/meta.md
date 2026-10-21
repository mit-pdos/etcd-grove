# raft-snapshot-during-apply-stale-confchange

## Security

Not a security report. In etcd it needs a membership change (`MemberAdd`/`MemberRemove`, root when auth is on) and a
follower behind the leader's compacted log at that moment; a client with ordinary access cannot cause it. etcd
uses v1 conf changes only, so there the outcome is a wrong configuration on one member, not the joint panic.

## Candidate

- **Finding**: `issues/raft-snapshot-during-apply-stale-confchange.md`
- **Target**: etcd-io/raft, `main` (also in v3.7.0, which etcd `main` uses: `raft.go` is identical)
- **Branch**: `fix/raft-snapshot-during-apply-stale-confchange` in `~/etcd-fixes/raft-snapshot-during-apply-stale-confchange`,
  three commits: a016d92 adds the test, which fails there; b556234 is the fix (`raft.go`, 27 lines added, 1
  changed); 9f77761 adds the changelog entry (48dafe8 cherry-picked). Rebuilt 2026-10-21 with a third fix, keeping
  the pre-snapshot configuration for the stale `ApplyConfChange` calls (the user's objection to the second fix,
  deferring the snapshot: it can make the leader send the snapshot again, in etcd a full database transfer;
  below). The second fix's branch is kept as local `backup/raft-snapshot-during-apply-stale-confchange-v2-defer`
  (48dafe8: a016d92, bfbb745, 48dafe8); the first push's head as `backup/raft-snapshot-during-apply-stale-confchange-v1`
  (da0e9bf).
- **Base**: upstream `main` 1931ff5beacc1e2539003c0c70f096285f04c425 (2026-10-19, the merge of #536). Rebased
  2026-10-21 from 638f42739. The test's lines (`rawnode_test.go#L718-L764`) are unchanged; the PR's permalinks
  are at 1931ff5. Not yet force-pushed: the fork still has `da0e9bf` (the deferral, on the old base); push with
  `git -C ~/etcd-fixes/raft-snapshot-during-apply-stale-confchange push --force-with-lease=fix/raft-snapshot-during-apply-stale-confchange:da0e9bf origin fix/raft-snapshot-during-apply-stale-confchange`
- **State**: draft (2026-10-21)
- **Upstream issue**: —
- **PR**: — (then replace `pull/TODO` in the changelog commit's `CHANGELOG/CHANGELOG-3.8.md` entry with its number)

etcd-io/raft has no issue template: the issue uses etcd's bug-report sections, with "Raft version" for etcd's
version and configuration sections.

Commit messages (drafts for the user to rewrite):

- `raft: test snapshot received while applying a conf change` (no body)
- `raft: keep the pre-snapshot configuration for conf changes being applied` — "Otherwise ApplyConfChange for
  entries being applied when a snapshot is restored applies their conf changes again, on top of the snapshot's
  configuration."
- `changelog: add entry for snapshot received while applying a conf change` (no body): Bug Fixes, "Fix wrong
  configuration or panic when a follower receives a snapshot while applying a conf change". The user is deciding
  whether to drop it (a backported bug fix gets none).

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

Independent of every other candidate. The fix touches `raft.go` in the `raft` struct, `appliedTo`, `Step`'s
`MsgStorageApplyResp` case, `restore` and `applyConfChange`; b556234 merges cleanly (`git merge-tree`, 2026-10-21)
with the code commits of `raft-confstate-unknown-fields-panic` and `raft-joint-empty-transition-panic` (each
branch's commit before its changelog tip; both are still on 638f42739) and with the tips of
`raft-advance-before-applyconfchange` and `raft-memorystorage-initialstate-unlocked`. The changelog commits of the
first two conflict with `main`'s `CHANGELOG-3.8.md` and with this one: whichever merges second needs a one-line
rebase. Not mentioned in the PR (not a split).

## Why the fix works

At the base, in the test's first case: node 2 steps `MsgApp` committing "add 4" at index 1; `Ready` hands it out
(`applying` 1, `applied` 0). The `MsgSnap` at index 2 is above the commit index, so `restore` restores it:
configuration `{1,2,3}`, commit 2. `ApplyConfChange("add 4")` then applies "add 4" to `{1,2,3}`: `{1,2,3,4}`. The
resent `MsgSnap` is at or below the commit index, so it is ignored, and node 2 keeps `{1,2,3,4}`. In the joint
case the restored configuration is already joint, and `EnterJoint` panics.

With the fix, `restore`, finding `applying > applied`, keeps the tracker it replaces (`confBeforeSnap`, the
configuration after the `ApplyConfChange` calls already made for the batch) and `applying` (1), then restores as
before: configuration `{1,2,3}`, commit 2, the snapshot in the next `Ready`, `MsgAppResp` at index 2 to the leader.
`ApplyConfChange("add 4")` runs the same `confchange.Changer` on the kept tracker, stores the result there and
returns its `ConfState`, `{1,2,3,4}`: what it returns at the base without the snapshot, the configuration at index
1. raft's configuration stays the snapshot's. `Advance` steps the `MsgStorageApplyResp` for index 1, which drops
the kept tracker. In the joint case the kept tracker is `{1,2,3}`, so `EnterJoint` succeeds there, and raft keeps
the snapshot's joint configuration.

- Which calls are stale: those made while the tracker is kept. Under doc.go's protocol the application calls
  `ApplyConfChange` for an entry after the `Ready` (or `MsgStorageApply`) that handed it out and before
  `Advance` (or that message's response). The tracker is kept from the restore to the response for the last
  entry handed out before it (`index >= confBeforeSnapIndex`), and while it is kept no newer entry is handed out
  (below), so every call meanwhile is for an entry at or below that index, which the snapshot includes; every
  later call is for an entry after the snapshot. Nothing counts calls: an application that does not call
  `ApplyConfChange` for a change it rejects (`Node.ApplyConfChange`'s comment) changes nothing.
- No newer entries while kept: in `RawNode` without `AsyncStorageWrites` (and `Node`) this holds anyway (the next
  `Ready` comes after `Advance`, and no entries are handed out until the snapshot is applied). With
  `AsyncStorageWrites`, the append thread may apply the snapshot (`appliedSnap`) before the apply thread answers
  the older `MsgStorageApply`; entries after the snapshot would then be handed out, and an `ApplyConfChange` for one
  of them could reach raft before the older response (raft's own async harness, `rafttest`, queues responses
  until they are delivered). So `appliedTo` sets `applyingEntsPaused` while the tracker is kept; the response that
  drops it runs `appliedTo`, which recomputes the flag. Checked by a temporary test (below): without that line,
  entry 3 is handed out before entry 1's response.
- The drop is in `Step`'s `MsgStorageApplyResp` case, not `appliedTo`: `appliedSnap` calls `appliedTo` with the
  snapshot's index, which may come first with `AsyncStorageWrites`. Every path that acknowledges applied entries
  steps that message (`RawNode.Advance`, `node.run`'s `Advance`, the application's with `AsyncStorageWrites`).
- A second snapshot restored while the tracker is kept keeps the first copy (the stale entries' configuration).
- Not touched: raft's own configuration (`r.trk`), so `switchToConfig`'s leader steps, the auto-leave proposal in
  `appliedTo` (reads `r.trk`), `pendingConfIndex`, and `node.run`'s removed-node check (compares `r.trk` before and
  after the call; the snapshot's configuration includes the node, as `restore` requires) see only the snapshot's
  configuration. A stale change that fails `confchange`'s checks panics as at the base, where it would apply to
  the same configuration.
- Without a snapshot restored while entries are being applied, nothing changes: the field stays nil.

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
compaction point while it is still applying an older batch. The test's second `Step(snap)` (a resend) is not needed by the fix; it stays so that the test asserts only the
guarantee (the follower ends with the snapshot's configuration) and not whether raft restores a snapshot at once,
later, or after a resend.

## Verification (go1.26.9 linux/amd64, 2026-10-21)

`TestRawNodeSnapshotDuringConfChangeApply` (`rawnode_test.go`, after `TestRawNodeRestartFromSnapshot`), two cases
in one table: v1 "add 4" with a snapshot of voters `{1,2,3}`; a `ConfChangeV2` "add 4" entering a joint
configuration (`JointExplicit`) with a snapshot in `(1 2 3 4)&&(1 2 3)`. Asserts only the guarantee: both halves of
node 2's voters equal the snapshot's.

- At the tests commit a016d92 (`go test -count=1 -run 'TestRawNodeSnapshotDuringConfChangeApply$' .`): fails,
  case 0 `expected: []uint64{0x1, 0x2, 0x3}`, `actual: []uint64{0x1, 0x2, 0x3, 0x4}`; case 1
  `panic: config is already joint`.
- At the fix commit b556234: passes; `go test -count=1 ./...` (raft, confchange, quorum, raftpb, rafttest,
  tracker) ok, also with `-race`; `gofmt -l .` empty; `go vet ./...` clean. 9f77761 differs only in the
  changelog. golangci-lint not installed, not run.
- Temporary tests, not on the branch (`go test -overlay` adding test files under `/tmp/snapscratch`), at the fix:
  - `ApplyConfChange`'s results (`RawNode`): the stale "add 4" returns `[1 2 3 4]` while raft's configuration
    stays `[1 2 3]`; `Advance` drops the kept tracker; after the snapshot's `Ready`, an "add 4" at index 3 changes
    raft's configuration to `[1 2 3 4]`.
  - `AsyncStorageWrites` `RawNode`, the snapshot applied by the append thread (`applied` 2) before the apply
    thread answers entry 1: a committed entry 3 (a conf change) is not handed out; the stale call returns
    `[1 2 3 4]` with raft at `[1 2 3]`; entry 1's response releases entry 3, whose call changes raft's
    configuration to `[1 2 3 4]`. Without the `applyingEntsPaused` line, entry 3 is handed out before entry 1's
    response (the test fails there).
  - `Node` (`node.run`): `Step(MsgSnap)` while the application holds the `Ready`; `ApplyConfChange` returns
    `[1 2 3 4]`; after `Advance` the next `Ready` carries the snapshot; `Status` shows `[1 2 3]`, commit 2.
  - The resend (a real leader `raft` whose log is compacted at index 2, against a `RawNode` follower holding a
    `Ready` with "add 4"; the leader steps `MsgSnapStatus` (`ReportSnapshot(SnapshotFinish)`) right after the
    follower steps the `MsgSnap`, then heartbeats while the follower applies; the follower's messages reach the
    leader only from `Ready`s; 30 rounds after `Advance`), counting the leader's `MsgSnap`s:

    | Variant | base | deferral (bfbb745) | this fix |
    |---|---|---|---|
    | as described | 1, follower `[1 2 3 4]` | 1 | 1 |
    | a heartbeat response sent before the snapshot reaches the leader after `ReportSnapshot` | 1, `[1 2 3 4]` | 2 | 1 |
    | the leader re-elected (term 2) while the follower applies | 1, `[1 2 3 4]` | 2 | 1 |

    Every run with a fix ends with the follower at `[1 2 3]` and the leader's progress `StateReplicate`.

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
from code only. With the fix, raft restores the snapshot at once, as at the base, and the stale call returns the
configuration at its index, which etcd stores in `ep.confState` and in its local snapshots (below).

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
  measured (the table above): the leader sends the snapshot a second time when, after `ReportSnapshot(SnapshotFinish)`,
  it gets any answer from the follower while the follower still defers (it probes past the snapshot, the follower
  rejects, its log is compacted): with `AsyncStorageWrites` the follower's heartbeat responses do that; without, a
  response the follower sent before the snapshot arrived and delivered after the POST returned. And when the
  term changes while the snapshot waits (an election), the kept message is dropped and the next leader sends
  another. In etcd each is a full database transfer. Also the restore waits for the batch.
- Skip stale calls by counting (raft counts the conf changes it hands out and the `ApplyConfChange` calls): wrong,
  an application that rejects a change "must not" call `ApplyConfChange`, so the count drifts.
- Skip stale calls by a flag (set when a snapshot is restored with `applying > applied`, cleared when `applied`
  reaches `applying`; meanwhile `ApplyConfChange` changes nothing and returns the current `ConfState`): 10 lines,
  restores at once, no resend, the branch's test passes. Rejected: a call for entry `i` returns the snapshot's
  later `ConfState`, and `ApplyConfChange`'s comment says the result "must be recorded in snapshots". Real in
  etcd (`server.go:978-999`, `2023`, `2102`): `applyConfChange` stores it in `ep.confState`; `applyAll` then waits for the raft loop's `notifyc` and runs
  `snapshotIfNeededAndCompactRaftLog`, whose `CreateSnapshot(ep.appliedi, ep.confState)` (and, past
  `SnapshotCount`, `SaveSnap`) races with the raft loop, which only after that `notifyc` sends the messages,
  calls `Advance`, gets the next `Ready` and saves the leader's snapshot; if the local snapshot wins
  (`ErrSnapOutOfDate` otherwise), a snapshot at `i` with the wrong configuration is in memory and possibly on
  disk, and a crash before the leader's snapshot is saved restarts from it (the configuration at `i` wrong, the
  conf changes after `i` in the WAL replayed on top of it). raft's own `rafttest` harness records each returned
  `ConfState` as the snapshot at that entry's index (`processApply`). Reasoning from code; not run on etcd.
- Track which entry each `ApplyConfChange` is for (`issues/raft-conf-lag-model/guard-fix.patch`, behind a
  `Config` flag): covers more (an `Advance` before `ApplyConfChange`), but a new option and API surface.
- This fix: keep the configuration the restore replaces while entries handed out before it are being applied,
  and apply the stale calls to it. Each call returns exactly what it returns at the base without the snapshot;
  raft's configuration is the snapshot's from the restore on, as at the base; the snapshot is restored at once,
  so nothing is sent twice; it does not count calls. The extra pause (no newer entries until the older ones are
  acknowledged) only matters with `AsyncStorageWrites`, where raft cannot otherwise tell a stale call from a new
  one.

Other questions:

- Cost: one `ProgressTracker` copy (configuration and progress map) held from the restore to the batch's
  `Advance`; with `AsyncStorageWrites`, entries after the snapshot wait for the older batch's response, only in
  this case. Nothing otherwise (a nil check per `appliedTo`, `MsgStorageApplyResp` and `applyConfChange`).
- `raft.go` sets `raftLog.applyingEntsPaused`, which `raftLog` otherwise computes from the outstanding size:
  the flag already means "hand out no committed entries until progress is acknowledged", and `appliedTo`
  recomputes it on every acknowledgement, so the override lasts exactly while the tracker is kept. A `raftLog`
  method would do the same in more lines.
- Liveness: the tracker is kept from the restore to the response for entries already handed out, which the
  application must deliver (`Advance`, or the `MsgStorageApply` response).
- Not covered: an application that calls `Advance` before `ApplyConfChange`, which doc.go's step 4 ("at any time
  after step 1") and `Node.Advance`'s comment allow. The tracker is then dropped at `Advance`, and the later
  `ApplyConfChange` is applied on top of the snapshot as before. That ordering breaks raft's other conf-change
  guards too (`issues/raft-advance-before-applyconfchange.md`); this fix assumes conf changes are applied before
  `Advance`, as doc.go's example loop does (and etcd, for a follower's `Ready` with a conf change).
- Comments: the field's doc says which calls are redirected and why; the one in `appliedTo` says why entries wait.
  None in `applyConfChange` or `restore` (the field's doc covers them).
- `ReportSnapshot`'s comment ("Calling ReportSnapshot with SnapshotFinish is a no-op"): not true at the base
  (`issues/raft-reportsnapshot-finish-not-noop.md`), not part of this PR; the fix does not depend on it.
- Backports: v3.7.0 has the same `restore`, `applyConfChange` and `appliedTo`; not tried on a release branch. The
  changelog entry is in `CHANGELOG-3.8.md` (v3.8.0, Bug Fixes): `main` is the 3.8 line. etcd uses v3.7.0, so the
  fix reaches etcd only with v3.8.0 or a v3.7.1 patch release, which raft has never made: the maintainers' call;
  if wanted, cherry-pick the fix commit to `release-3.7` in a separate PR.

## check.py (2026-10-21)

No FAIL. WARNs, decided:

- The comments added: kept. The field's doc follows the `raft` struct's convention (every field has one) and says
  which `ApplyConfChange` calls go to the kept configuration and why (the snapshot includes their entries), which
  the code does not show; the one in `appliedTo` says why newer entries wait.
- The issue's 260 words (aim 250): kept; it shows two cases (wrong configuration and panic). Unchanged by the new
  fix.
- The PR's 125 words (aim 90): kept; the approved raft example has 136, and the change needs both halves (the
  copy, the pause).
