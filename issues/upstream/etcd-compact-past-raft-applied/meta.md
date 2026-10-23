# etcd-compact-past-raft-applied

- **Finding**: `issues/etcd-compact-past-raft-applied.md`
- **Target**: etcd-io/etcd, `main`
- **Branch**: `fix/etcd-compact-past-raft-applied` in `~/etcd-fixes/etcd-compact-past-raft-applied`, two commits
  (rebuilt 2026-10-23 on the new base, both cherry-picked unchanged): e0846e9f3 adds the test, which fails there;
  70f92483e is the fix. Not pushed (`git ls-remote origin` has no `fix/etcd-compact-past-raft-applied`). The
  previous head, on 7ff040cb8, is kept as `backup/etcd-compact-past-raft-applied-v1` (be0ad9592; 1fb0e1926 its
  tests commit; 8967f11ae before its message was rewritten, same tree).
- **Base**: upstream `main` 3aaab3479b6c4f5fe1b2b8f33437093c2caae88a (2026-10-22). The 22 commits since 7ff040cb8
  touch none of `server/etcdserver/`, `tests/integration/v3_leadership_test.go`, nor raft's version (v3.7.0,
  b867cf13f): `raftNode.start`, `applyAll` and `compactRaftLog` are as in the finding, at the same lines.
- **State**: draft

Commit messages (drafts for the user to rewrite):

- `tests/integration: test leader transfer to a member replaying its WAL` (no body)
- `etcdserver: compact the raft log only after raft advances`, body: "Raft reads its log from its applied index
  until Advance, so a campaign right after the compaction could panic."

Push (once approved): `git -C ~/etcd-fixes/etcd-compact-past-raft-applied push origin fix/etcd-compact-past-raft-applied`
(never pushed, so no `--force-with-lease`);
then check the issue's test link (`#L185-L222`, doc comment to closing brace) on GitHub.

## Impact: does a restart clear it? (the user's question, 2026-10-23)

Yes. The panic kills one member's process, the one that receives the transfer (or starts an election) in the
window; the rest of the cluster keeps serving. Nothing on disk is damaged: the entries and hard state were saved
before the window opens (`Save` precedes `notifyc`), and the backend has the applied entries with their consistent
index. Checked 2026-10-23: the panicked test process leaves the member's data directory behind
(`/tmp/TestMoveLeaderToRestartedMember570913632/004/...`); a copy, started alone with `etcd` built from the base
(`go build` in `server/` at the tests commit), logged `restore consistentIndex` 158, `kvstore restored` with
`current-rev` 151 (all 150 puts), `restarting local member` with `commit-index` 158, `newRaft ... applied: 0,
lastindex: 158`, and then campaigned (pre-vote, no peers) four times without panicking. It could not rejoin, since
its peers were gone with the test.

What a restart does not do: by code reading, it reopens the window. A member with no snapshot on disk (fewer than
`--snapshot-count` entries since the last one, 10000 by default) restarts with raft's applied index 0; if it has
more than 100 entries to replay (`memorySnapshotCount`), the first batch makes an in-memory snapshot and compacts at
index 1 (or `appliedi - SnapshotCatchUpEntries`), above 0, before `Advance`. With a snapshot on disk at index S, the
window opens only if the first batch holds more than `SnapshotCatchUpEntries` (5000) entries, as in steady state. So
a transfer or election that lands right after such a restart can crash the member again, but nothing makes it land
there repeatedly: no crash loop is expected. The issue says this, marked as code reading.

So the impact is a rare crash of one member, cleared by the restart a supervisor would do anyway; the reasons to
upstream it are that it breaks `MemoryStorage.Compact`'s documented precondition, that the window widens with any
proposal to compact more often (#17098), and that the fix is a two-line ordering change. Not measured: how often the
window is hit without the failpoint (its width is the time between the follower's `notifyc` send and `Advance`,
which includes `transport.Send`; not timed).

## Security

Not a security report by the skill's criterion: the trigger is a leader transfer (`MoveLeader`, an admin
operation) or an election that starts in a window of microseconds after a member applies a batch, and a single
member crashes (and restarts cleanly). No client with ordinary access can aim it.

## Duplicates checked (2026-10-21, with the token; rechecked 2026-10-23)

2026-10-23 (unauthenticated): `"error scanning unapplied entries"` (0), `"unavailable due to compaction" panic` (5:
the known #12134, #9079, #7470, and #16423/#9685 about raftexample), `compactRaftLog Advance` (0), `raftAdvancedC`
(2: #22459, a test cleanup, and #20967, an upgrade issue; unrelated), raft `hasUnappliedConfChanges compaction` (0),
`compaction panic` updated since 2026-10-20 (#22633, open: a v3.7.2 startup panic "unmarshal should never fail"
replaying v2 WAL entries; a different panic). No duplicate, no open PR.

2026-10-21 searches (issues and PRs): `"error scanning unapplied entries"`, `"unavailable due to compaction" panic`,
`compact raft log applied Advance`, `compactRaftLog`, `raftAdvancedC`, raft `hasUnappliedConfChanges`, raft
`Compact applied application responsibility`. No duplicate, no open PR fixing it. Related:

- etcd-io/etcd#9079 (closed, stale): the same panic message ("unexpected error getting unapplied entries"), etcd 3.1,
  after raft restored a leader snapshot; a different path (raft v3.7 refuses to campaign with a pending snapshot).
- etcd-io/etcd#12134 (merged): made `MsgTimeoutNow` go through the unapplied conf-change scan that panics here.
- etcd-io/etcd#7470 (closed): compaction racing an incoming snapshot; different path.
- etcd-io/etcd#18825 (merged, v3.6.0): in-memory snapshots every 100 entries, which make the restart trigger
  (first memory snapshot while raft's applied index is 0, compact index 1) reachable with defaults.
- etcd-io/etcd#17098 (closed) / #18459 (closed, unmerged): proposals to compact the raft log more often (after every
  apply); they would make this window matter on every batch, so the fix fits them.
- etcd-io/raft#32 (merged): paginated the scan; etcd-io/raft#469 (open, TLA+ only).

## Why the fix works

At the base, for each `Ready`, `raftNode.start` hands the committed entries to the apply loop (`applyc`), persists
and appends the entries, signals `notifyc`, and then calls `Advance`, which moves raft's `raftLog.applied` (until
then, raft has only moved `applying`). `applyAll` applies the batch, waits for `notifyc`, and then
`snapshotIfNeededAndCompactRaftLog` compacts `MemoryStorage` at `appliedi - SnapshotCatchUpEntries` (or `1` while
`appliedi <= SnapshotCatchUpEntries`). So between `notifyc` and `Advance`, the compact index can exceed
`raftLog.applied` (after a restart with no disk snapshot: `applied = 0`, compact index `1`; in steady state, a batch
of more than `SnapshotCatchUpEntries` entries). A `MsgHup` in that window (a `MsgTimeoutNow`, an election
timeout or `Campaign`) runs `hasUnappliedConfChanges`, which scans `[applied+1, committed+1)`, hits
`ErrCompacted` and panics.

With the fix, `raftNode.start` closes `raftAdvancedC` after every `Advance` (it sent on it only for batches with a
conf change, for `configure`'s waiter, which a close serves as well), and `applyAll` waits for it after `notifyc`,
before snapshotting and compacting. So the compact index is at most the batch's last index, which raft's applied
index covers by then. In the test, the restarted member's raft scans `[1, 159)`, finds the bootstrap conf changes
not yet applied by raft, and refuses the campaign ("cannot campaign at term 2 since there are still pending
configuration changes to apply"); the transfer times out and the member serves the next put.

No deadlock: the raft routine's only wait on the apply loop between `applyc` and `Advance` is a follower's second
`notifyc` send for a batch with a conf change, which `applyAll`'s `<-apply.notifyc` releases before the new wait.
Everything else on that path does not block on the apply loop (`processMessages` drops a `MsgSnap` when `msgSnapC`
is full, rafthttp's `Send` drops when a peer's buffer is full, `Advance` returns on `node.run`'s `advancec`), and
its failures are `lg.Fatal`, which exits the process.

Shutdown: the new wait is unconditional, like `<-apply.notifyc` before it, and for the same reason. The raft routine
returns without reaching `Advance` only on `r.stopped` (the `readStateC` send and the `applyc` send, before the
job exists; the conf-change `notifyc` send, after the job has read `notifyc`). `r.stopped` is signalled only by
`raftNode.stop`, which `EtcdServer.run`'s deferred shutdown calls after `sched.Stop()` returns, and the FIFO
scheduler's `Stop` runs every pending job to completion before returning. So while any `applyAll` waits, the raft
routine cannot be stopped, and it reaches `close(raftAdvancedC)`. A `select` on `s.stopping` (as in the finding's
first patch) is not needed, and would let a job compact before `Advance` during shutdown. The wait also makes
`configure`'s existing unconditional `<-resp.raftAdvanceC` safer: before, `sched.Stop()` could return while the raft
routine was still in the conf-change batch, and that `select` could then pick `r.stopped` and never send.

No throughput cost: the next batch is handed out only after this `Advance`, so the
wait delays only the snapshot step of the current job.

The test is the finding's end-to-end reproduction with the existing failpoint `raftBeforeFollowerSend` (between
`notifyc` and `Advance`, on followers; the finding's repro used a new member-specific failpoint, which a tests-only
commit cannot add) set to `sleep("2s")` only after the puts, to widen the window. Everything else is the ordinary
protocol: a restart, a `MoveLeader` from the leader. It asserts the guarantee (the transferee does not crash and
serves a put), not whether the transfer succeeds. Like the other failpoint tests in `tests/integration`, it skips
without `gofail enable`. CI runs it: the Prow presubmits `pull-etcd-integration-{1,2,4}-cpu-{amd64,arm64}`
(kubernetes/test-infra `config/jobs/etcd/etcd-presubmits.yaml`, checked 2026-10-21) run `make gofail-enable` before
`make test-integration`, as etcd-io/etcd 6d79b8621 set up for the then GitHub Actions jobs.

## If a reviewer asks: the candidate layers and fixes

1. **etcd, `applyAll` waits for `Advance` before compacting (chosen).** The defect is etcd breaking a documented
   precondition of `MemoryStorage.Compact` ("It is the application's responsibility to not attempt to compact an
   index greater than raftLog.applied"), and `raftAdvancedC` already exists to say exactly that `raftLog.applied`
   has advanced (its field comment); its use was restricted to conf-change batches only because it was sent, not
   closed. One check where every compaction goes through (`snapshotIfNeededAndCompactRaftLog` is called only from
   `applyAll`).
2. **raft, tolerate the compaction in `hasUnappliedConfChanges`** (treat `ErrCompacted` as "pending", or scan from
   `max(applied, firstIndex-1)+1`). Not the root cause: raft documents the bound, and it genuinely needs the entries
   in `(applied, applying]` until `Advance` (they may hold conf changes etcd has not applied; scanning from
   `firstIndex` would skip them and allow a campaign with a stale configuration). It would also need a raft release
   and an etcd bump. Raft maintainers would point to `Compact`'s doc.
3. **etcd, bound the compact index by the applied index before the batch** (`min(compacti, appliedi before
   applyEntries)`, which raft had applied when it handed out the batch). Correct, but it keeps the window and relies
   on an invariant between etcd's and raft's applied indexes that nothing states (and a `Ready` with a snapshot
   moves both). It compacts one batch less, too. A workaround at the caller.
4. **etcd, `compacti = min(compacti, s.r.Status().Applied)`.** Reads raft's applied index through `node.run`'s
   status channel; correct (it only grows), but a round trip per compaction and an ad-hoc bound where an ordering
   signal exists.
5. **etcd, reorder `raftNode.start`: `Advance` before `notifyc`.** The simplest reorder, but wrong: a follower must not
   `Advance` past a conf change before the apply loop has applied it (the second `notifyc` handshake exists for
   this; otherwise raft could campaign with the old configuration). Not run: rejected by reading.
6. **Wait only when a snapshot is due** (inside `snapshotIfNeededAndCompactRaftLog`). Saves nothing measurable (see
   "no throughput cost"), and needs the channel passed down; the unconditional wait is simpler.

The snapshot itself (`CreateSnapshot(appliedi)` before `Advance`) is harmless to raft (a committed, applied
prefix); it moves with the compaction anyway.

## Verification

Rerun 2026-10-23 at the rebuilt branch (go1.27.3 linux/amd64, gofail v0.2.0), with failpoints enabled as below in a
test binary built at each commit (`gofail enable server/etcdserver/`, `go get go.etcd.io/gofail@v0.2.0` in `server/`,
`go test -c ./integration/` in `tests/`, then the tree restored):

- At the tests commit e0846e9f3: panics 3 runs of 3, `panic: error scanning unapplied entries [1, 159): requested
  index is unavailable due to compaction` from `hasUnappliedConfChanges` / `hup` / `stepFollower` on the
  `MsgTimeoutNow`; the output in `issue.md` is from the first run.
- At the fix 70f92483e: passes 5 of 5, and 3 of 3 with `-test.cpu 1`; the log shows `cannot campaign at term 2 since
  there are still pending configuration changes to apply`. With the same binary, `-test.run
  'TestMoveLeader|TestTransferLeader|TestFirstCommit|TestMember|TestRestart|TestV3LeaseRevoke|TestV3RangeStream|TestSnapshot'`
  passes. Without failpoints: `cd server && go test ./etcdserver/...` ok; `go vet ./etcdserver/` and `go vet
  ./integration/` clean; `gofmt -l` of the changed files empty; `cd tests && go test ./integration/ -count=1 -timeout 50m` ok (482 s;
  the new test skips there, as it needs failpoints).
- Restart of the panicked member: above, "Impact".

Before the rebuild (at 7ff040cb8, go1.27.2):

Failpoints enabled as `tests/robustness/Makefile`'s `gofail-enable` for `server/etcdserver/` only
(`gofail enable server/etcdserver/ && (cd server && go get go.etcd.io/gofail@v0.2.0)`; reverted before committing).

- At the tests commit 1fb0e1926 (`cd tests && go test ./integration/ -run 'TestMoveLeaderToRestartedMember$'
  -count=1 -v`): panics, 3 runs of 3 (and 4 of 4 with the first draft of the test): `panic: error scanning unapplied
  entries [1, 159): requested index is unavailable due to compaction` from `hasUnappliedConfChanges` / `hup` /
  `stepFollower` (`MsgTimeoutNow`); the output in `issue.md` is from one of these runs.
- At the fix 8967f11ae: passes, 5 runs of 5 (about 6.7 s each); the log shows the refused campaign.
- Rerun 2026-10-21 after the message rewrite (go1.27.2): at 1fb0e1926 panics 3 of 3 (`[1, 159)`, as above); at
  be0ad9592 passes 5 of 5 and 3 of 3 with `-cpu 1` (as the 1-CPU CI job), and, failpoints still enabled,
  `go test ./integration/ -run 'TestMoveLeader|TestTransferLeader|TestFirstCommit|TestMember|TestRestart|TestV3LeaseRevoke|TestV3RangeStream|TestSnapshot'`
  ok and `cd server && go test ./etcdserver/...` ok; without failpoints `go test ./etcdserver/...` ok, `go vet` of
  `server/etcdserver` and `tests/integration` clean, `gofmt -l` empty.
- A first draft with `sleep("5s")` and no `WaitLeader` failed at the fix with "request timed out": a 5 s sleep in
  every follower made the leader lose its quorum (CheckQuorum) and the next election slow. Shortened to 2 s and
  `WaitLeader` added (setup only).
- At the fix, without failpoints: `cd server && go test ./etcdserver/...` ok (includes `TestConfigChangeBlocksApply`,
  which reads `raftAdvancedC`); `go vet ./etcdserver/` clean; `gofmt -l` empty.
- At the fix, without failpoints: `cd tests && go test ./integration/` ok (472 s; the new test skips there, as it needs failpoints).

Not run: `tests/e2e`, `tests/robustness`, `make verify` (golangci-lint).

## Review (2026-10-21)

By hand, as a maintainer: `raftAdvancedC`'s readers are `configure` (`<-resp.raftAdvanceC`, served by a close),
`applyAll` (new) and `TestConfigChangeBlocksApply` (reads once, served by a close); the server tests that call
`apply` directly pass their own channel. `toApply`'s comment no longer restricts it to conf changes. No other code
compacts `raftStorage`. No other comment claims the old behavior. No new bug found.

Second pass (2026-10-21), as a maintainer: every return of the raft routine and the scheduler's `Stop` checked
(above, "Shutdown"); no hang, so the fix is unchanged. Readers of `raftAdvancedC` rechecked: `configure` and
`TestConfigChangeBlocksApply` read once, served by a close; `TestApplyConfigChangeUpdatesConsistIndex` and
`TestApplyMultiConfChangeShouldStop` (server_test.go) pass their own channel with one value to `apply`; no test
calls `applyAll`. The test matches the package's failpoint tests (`SkipIfNoGoFail`, `gofail.Enable` mid-test,
`TestV3RangeStreamWriteBetweenChunks`). Only the fix commit's body was rewritten, and `pr.md` shortened. Third pass (2026-10-23, after the rebuild): every send on `notifyc` against its reads, for each kind of batch (a
follower's snapshot batch sends at the snapshot, before `processMessages` and, with a conf change, once more; reads
are `applySnapshot`'s and `applyAll`'s): each send completes before `Advance`, so `close(raftAdvancedC)` is always
reached while the job waits. No change; no new bug. The `check.py` WARNs on the fix's comments are
kept, and so is the issue's length (about 290 words of prose, over the 250 aimed for: the impact paragraph answers whether a restart clears the crash, which a maintainer triaging a panic asks first): the field comment replaces one that restricted the channel to conf changes, the `notify etcdserver` line is
the existing comment re-indented, and the `applyAll` comment says why the wait is there.
