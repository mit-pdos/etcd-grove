# etcd-merged-snapshot-stale-term

## Security classification

Not a security report, but the user should confirm it. The worst effect is a raft panic (`need non-empty snapshot`)
at a leader of an intermediate term, which ends that member's process. No client with ordinary access can trigger
it: it needs a leader's save of a Ready to stall for longer than an election timeout (a slow disk), two or more
followers behind the leader's compacted log, a partition that keeps one of them at the old term, and, for the panic,
a gap of two terms with the intermediate leader still up.

## Candidate

- **Finding**: `issues/etcd-merged-snapshot-stale-term.md`
- **Target**: etcd-io/etcd, `main`. Since #7513 (2017) the merged snapshot's term is `etcdProgress.appliedt`, with
  `m.Term` unchanged. The release branches likely have the bug too (not checked).
- **Branch**: `fix/etcd-merged-snapshot-stale-term` in `~/etcd-fixes/etcd-merged-snapshot-stale-term`, two commits:
  01009c61f (`etcdserver: test the term of a merged snapshot`) adds the test, which fails there; f81ca1509
  (`etcdserver: send a queued MsgSnap only while raft is at its term`) is the fix. Not pushed.
- **Base**: upstream `main` 6782f5229b8a6dbc5f6d421107fd70d66de98694 (2026-10-19). `processMessages`, `applyAll`'s
  `msgSnapC` branch and `createMergedSnapshotMessage` match the finding's description at the fork pin.
  `applyAll` on `main` does not wait for `raftAdvancedC` (that wait is a fork fix,
  `issues/etcd-compact-past-raft-applied.md`). The bug does not depend on it.
- **State**: draft
- **Upstream issue**: —
- **PR**: —

## Duplicates checked (2026-10-19)

Five searches: `createMergedSnapshotMessage`, `merged snapshot term` and `msgSnapC` (etcd-io/etcd), `"need non-empty
snapshot"` (etcd-io/etcd and etcd-io/raft), and `snapshot term greater` (etcd-io/raft). None is a duplicate, and no
open PR fixes it. Related, different:

- etcd-io/etcd#7470 (closed) and #7513 (merged): the merge looked up the snapshot's term in a compacted raft log.
  #7513 introduced `appliedt`, which is the term this bug is about.
- etcd-io/etcd#4096 and #4062 (closed, 2015): how merging is scheduled.
- etcd-io/raft#47 (open PR, pav-kv, 2023): "raft: fix out-of-order terms". It states the invariant this bug breaks,
  that a `MsgSnap` `m` has `m.Term >= m.Snapshot.Metadata.Term` because the leader knows no higher term than its
  own, and says only a raft test broke it. It is worth citing if a reviewer asks what grounds the expectation. It
  would turn the intermediate leader's panic into an earlier one (`appending out-of-order term`) and does not fix
  etcd.
- etcd-io/raft#108 (open): the same `need non-empty snapshot` panic with a different cause, `MemoryStorage.Snapshot`
  in a fuzzing harness.

## Verification (go1.27.2 linux/amd64)

`TestMergedSnapshotTerm` (in `server/etcdserver/server_test.go`, after `TestSnapshotOrdering`, through the same
harness: `newNopReadyNode`, `newSnapTransporter`, the real `raftNode` loop and `applyAll`) is the issue's example.

- At the tests commit 01009c61f (`cd server; go test ./etcdserver -run TestMergedSnapshotTerm -count=20`): fails 20
  of 20, `"2" is not less than or equal to "1"`, `snapshot term of the MsgSnap to 5`.
- At the fix commit f81ca1509: the same command passes 20 of 20. In `server/`, `go test ./... -count=1` is ok
  (every package), `go vet ./etcdserver/` is clean and `gofmt -l` is empty. `cd tests; go test ./integration/ -run
  'Snapshot|Snap' -count=1` is ok.

Not run: `tests/e2e`, the whole of `tests/integration`, `make verify` (golangci-lint). The scenario end to end (a
real cluster with a stalled fsync and an asymmetric partition) was not reproduced. The finding's raft-level tests
show that raft reaches the state (`merged_snapshot_stale_term_test.go`) and the gap-of-two panic
(`stale_term_gap2_ack_test.go`, with hand-built messages), at raft v3.7.0 and the fork.

## Why the test shows the bug and not a misuse

The fake raft node hands out the Readys raft hands out in the finding's scenario, which `merged_snapshot_stale_term_test.go`
plays with five real `RawNode`s:

1. A follower's Ready at term 2, with member 2 as leader, the committed term-1 entry and two term-1 `MsgSnap`s.
   raft emits these when the node stepped down during the stalled save: messages made while leader stay in `msgs`
   until the next Ready.
2. The commit of member 2's term-2 entry.
3. A leader's Ready at term 3 with a term-3 `MsgSnap` to member 3.

Ready 3 is there only as a sync point. Jobs run in order, and `sendMergedSnap` calls `SendSnapshot` within the job,
so once the message to 3 arrives, every earlier merged message has been sent. With the fix, Ready 3's message is
still sent, so the test also checks that the fix does not drop a current message. The assertion is the guarantee:
no sent `MsgSnap` has a snapshot term above its own term. raft's own `MsgSnap`s always have it, because a leader's
snapshot is of its log, whose terms are at most its term. etcd's server code uses only `Ready`'s documented fields.

## Why the fix works

At the base, `processMessages` queues every `MsgSnap` on `msgSnapC` (16 slots). Each `applyAll` job, after applying
its batch and waiting for `notifyc`, takes at most one queued message and merges it with `(appliedi, appliedt)`. At
the base nothing ties the message's term to what was applied:

- In the scenario, job 1 takes member 4's message.
- Job 2 applies the term-2 entry and takes member 5's message, which is sent as term 1 with a term-2 snapshot.

With the fix, the raft goroutine records `rd.HardState.Term` whenever a Ready's HardState is non-empty and passes
it in `toApply.raftTerm`. `applyAll` merges a message only if `m.Term >= raftTerm`. Every entry applied up to batch
`k` was committed in a Ready at or before `k`, and that Ready's HardState carried the committed index and the term,
so the applied data's term, and the term it was committed at, are at most `raftTerm`. If `m.Term >= raftTerm`, the
node made `m` as leader of `m.Term`, and everything applied was committed in its log at or before that term: the
merged snapshot is a snapshot of that leader's committed log, as raft's own would be. If `m.Term < raftTerm`, raft
has left `m.Term`. Every term change resets the progress of every peer (`raft.reset`), so no leader waits for
`m`'s `ReportSnapshot`, and dropping it without a report leaves nothing stuck. The current leader, if it needs to,
sends its own `MsgSnap`. This also excludes the finding's second shape (data of `m.Term` or older, committed by a
later leader), because that commit raised the HardState term first.

## If a reviewer asks

- **Why `>=` and not `==`** (the verified fork's version, de825d8c6, uses `==`): raft can run several Readys ahead
  of the apply jobs. The run loop schedules a job as soon as it receives the batch, and `applyAll` does not wait for
  raft. So job `k` can take a `MsgSnap` that raft made in a later Ready, at a term newer than batch `k`'s. Merging
  that message is safe: the data is older than its term. Dropping it without a `ReportSnapshot` would leave the
  leader's progress for that peer in `StateSnapshot` until the next term change. Likewise `raftTerm` is 0 until the
  first non-empty HardState after a restart. With `>=` that case keeps today's behavior.
- **Why not `s.Term()` or `s.isLeader()`**: `s.Term()` is the applied entry's term, which is exactly what may be
  newer. `isLeader()` holds again after a re-election at a later term.
- **Why not `s.r.Status()` in `applyAll`**: it would work (merge only if leader at `m.Term`), but it is a round trip
  to raft's goroutine in every job that takes a message, and it is no more precise: the message is made at
  `m.Term` either way.
- **Why not restamp `m.Term` with `appliedt`**: the sender need not have been leader at `appliedt`.
- **Why not fix it in raft** (reject a `MsgSnap` whose snapshot term exceeds its term in `restore`): the receiver
  cannot tell a stale merge from a valid one in the second shape (data committed later, of an old term), and raft's
  own messages never violate it. A raft-side check would be defense in depth (raft#47's direction), not the fix.
- **Cost**: one `uint64` per batch and a comparison per queued `MsgSnap`.
- **Backport**: the release branches were not checked. The fix is self-contained.

## check.py

No FAIL. WARNs kept:

- The two comments in the fix stay. `raftTerm`'s field comment matches its neighbours in `toApply`, and the one
  in `applyAll` says why a message is dropped.
- The issue's 355 words of prose cover a three-step scenario and its impact (the panic), which a maintainer needs
  in order to care.
- The PR's 117 words hold three permalinks and one sentence of change.
