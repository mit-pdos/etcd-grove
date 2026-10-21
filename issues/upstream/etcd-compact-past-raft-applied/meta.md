# etcd-compact-past-raft-applied

- **Finding**: `issues/etcd-compact-past-raft-applied.md`
- **Target**: etcd-io/etcd, `main`
- **Branch**: `fix/etcd-compact-past-raft-applied` in `~/etcd-fixes/etcd-compact-past-raft-applied`, two commits
  (2026-10-21): 1fb0e1926 adds the test, which fails there; 8967f11ae is the fix. Not pushed.
- **Base**: upstream `main` 7ff040cb84c9944d0c38a9f0dc9f12ed9c58223b (2026-10-21). `server/etcdserver/raft.go` and
  `server.go`'s `applyAll`/`compactRaftLog` are as in the finding (checked at 22cc5d9ac); raft `v3.7.0`
  (b867cf13f).
- **State**: draft

Commit messages (drafts for the user to rewrite):

- `tests/integration: test leader transfer to a member replaying its WAL` (no body)
- `etcdserver: compact the raft log only after raft advances`, body: "The raft log was compacted before raft
  advanced past the applied entries, while raft still reads the log from its applied index."

Push (once approved): `git -C ~/etcd-fixes/etcd-compact-past-raft-applied push origin fix/etcd-compact-past-raft-applied`;
then check the issue's test link (`#L185-L222`, doc comment to closing brace) on GitHub.

## Security

Not a security report by the skill's criterion: the trigger is a leader transfer (`MoveLeader`, an admin
operation) or an election that starts in a window of microseconds after a member applies a batch, and a single
member crashes (and restarts cleanly). No client with ordinary access can aim it.

## Duplicates checked (2026-10-21, with the token)

Searches (issues and PRs): `"error scanning unapplied entries"`, `"unavailable due to compaction" panic`,
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
Shutdown: `raftNode.stop` runs only after the scheduler stops, and nothing between `applyc` and `Advance` waits on
the job, so `Advance` comes. No throughput cost: the next batch is handed out only after this `Advance`, so the
wait delays only the snapshot step of the current job.

The test is the finding's end-to-end reproduction with the existing failpoint `raftBeforeFollowerSend` (between
`notifyc` and `Advance`, on followers; the finding's repro used a new member-specific failpoint, which a tests-only
commit cannot add) set to `sleep("2s")` only after the puts, to widen the window. Everything else is the ordinary
protocol: a restart, a `MoveLeader` from the leader. It asserts the guarantee (the transferee does not crash and
serves a put), not whether the transfer succeeds. Like the other failpoint tests in `tests/integration`, it skips
without `gofail enable`.

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

## Verification (go1.27.2 linux/amd64, gofail v0.2.0)

Failpoints enabled as `tests/robustness/Makefile`'s `gofail-enable` for `server/etcdserver/` only
(`gofail enable server/etcdserver/ && (cd server && go get go.etcd.io/gofail@v0.2.0)`; reverted before committing).

- At the tests commit 1fb0e1926 (`cd tests && go test ./integration/ -run 'TestMoveLeaderToRestartedMember$'
  -count=1 -v`): panics, 3 runs of 3 (and 4 of 4 with the first draft of the test): `panic: error scanning unapplied
  entries [1, 159): requested index is unavailable due to compaction` from `hasUnappliedConfChanges` / `hup` /
  `stepFollower` (`MsgTimeoutNow`); the output in `issue.md` is from one of these runs.
- At the fix 8967f11ae: passes, 5 runs of 5 (about 6.7 s each); the log shows the refused campaign.
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
