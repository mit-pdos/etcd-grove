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
  1645e3a35 (`etcdserver: test the term of a merged snapshot`) adds the test, which fails there; 4a88c8a8e
  (`etcdserver: drop a queued MsgSnap older than the applied term`) is the fix. Never pushed (`git ls-remote
  origin`, 2026-10-23). The previous head, c5630c231 (on bf9cadf04), is kept as the local branch
  `backup/etcd-merged-snapshot-stale-term-v1`.
- **Base**: upstream `main` 3aaab3479b6c4f5fe1b2b8f33437093c2caae88a (2026-10-23; rebuilt from bf9cadf04, whose 20
  later commits are dependency bumps, CI and changelogs, touching none of these files; earlier, 6782f5229). `processMessages`, `applyAll`'s `msgSnapC` branch and
  `createMergedSnapshotMessage` match the finding's description at the fork pin. `applyAll` on `main` does not wait
  for `raftAdvancedC` (that wait is a fork fix, `issues/etcd-compact-past-raft-applied.md`). The bug does not depend
  on it.
- **State**: draft (revised 2026-10-23: the issue and the test are about the invariant the receiver breaks, its
  log term above its current term, with the panic as a consequence; rebuilt on 3aaab3479)
- **Upstream issue**: —
- **PR**: —

## Duplicates checked (2026-10-19, rechecked 2026-10-21 and 2026-10-23)

2026-10-23 (github.com issue search, issues and PRs): `"merged snapshot" term`, `MsgSnap term updated:>=2026-10-21`
(none), `"need non-empty snapshot"`, `snapshot term greater current term`, `createMergedSnapshotMessage`. Nothing
new: #18459, #18235 (closed PRs) only contain the panic string; #22524 (open) is about readiness after a snapshot;
#22184/#22185 (open) are a lock-order inversion. No open PR fixes it.

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

Rechecked 2026-10-21 (authenticated search, issues and PRs): `createMergedSnapshotMessage`, `msgSnapC`, `snapshot
stale term` (etcd-io/etcd), and `MsgSnap term` / `snapshot term` updated since 2026-10-19 (etcd-io/etcd,
etcd-io/raft). Nothing new; #22516/#22524 (open, a member catching up from a snapshot stays unpublished) and #22510
are about the receiver's publish, not the message's term.

## Verification (go1.27.3 linux/amd64, 2026-10-23, at base 3aaab3479)

`TestMergedSnapshotTerm` (in `server/etcdserver/server_test.go`, after `TestSnapshotOrdering`, through the same
harness: `newNopReadyNode`, `newSnapTransporter`, the real `raftNode` loop and `applyAll`) is the issue's example.
Since 2026-10-23 it also delivers the merged `MsgSnap` to member 5, a real `raft.Node` (`raft.RestartNode` over a
`MemoryStorage` at term 1, as `realisticRaftNode` builds one but with the term set; that helper leaves the term at
0), and asserts the guarantee the receiver loses: its last log term (the installed snapshot's) is at most its term.
Both members start from the same snapshot at index 1, term 1, with voters 1 to 5 (raft drops a snapshot whose
`ConfState` lacks the receiver).

- At the tests commit 1645e3a35 (`cd server; go test ./etcdserver -run 'TestMergedSnapshotTerm$' -count=20`):
  fails 20 of 20, `"2" is not less than or equal to "1"`, `last log term of member 5, at term 1, after it installs
  the MsgSnap`; raft logs `5 [commit: 3, lastindex: 3, lastterm: 2] restored snapshot [index: 3, term: 2]` after `5
  became follower at term 1` (the issue's output).
- At the fix commit 4a88c8a8e: the same command passes 20 of 20; `go test ./etcdserver/... -count=1` is ok (every
  package); `go test -race ./etcdserver -count=1` is ok; `go vet ./etcdserver/` is clean and `gofmt -l etcdserver`
  is empty.
- Siblings that touch the same files (2026-10-23): `git merge-tree --write-tree` of this branch with
  `fix/etcd-alarm-store-snapshot-race` (7569d2bbd), `fix/etcd-auth-snapshot-closed-backend-panic` (2680ccf2b, not
  yet rebuilt on 3aaab3479) and `fix/etcd-compact-past-raft-applied` (70f92483e, which also edits `applyAll`, three
  lines above this change) is clean for each; the merge with the last builds (`go build ./...` in `server`), vets
  and passes `go test ./etcdserver` (the other two merges were built on 2026-10-21 only). No conflict note is
  needed in `pr.md`.

Not run: `tests/e2e`, `tests/integration` (run on the previous version of the fix, 2026-10-19: `-run
'Snapshot|Snap'` ok), `make verify` (golangci-lint). The scenario end to end (a real cluster with a stalled fsync
and an asymmetric partition) was not reproduced. The finding's raft-level tests show that raft reaches the state
(`merged_snapshot_stale_term_test.go`) and the gap-of-two panic (`stale_term_gap2_ack_test.go`, with hand-built
messages), at raft v3.7.0 and the fork.

## The invariant

The issue leads with Raft's invariant that a member's current term is at least the term of every entry in its log
(a member at term `T` knows of no later term, and every entry was made by the leader of its term). raft keeps it for
its own messages: a leader's `MsgSnap` carries a snapshot of its own log, so `m.Term >= m.Snapshot.Metadata.Term`
(etcd-io/raft#47 states this form), and a receiver at a lower term first raises its term to `m.Term`. The merged
message breaks it at the receiver: member 5 at term 1 restores a snapshot of term 2 (raft's own log line shows
`lastterm: 2` after `became follower at term 1`). The gap-of-two panic is a consequence of that state, in the issue's
"Anything else".

## Why the test shows the bug and not a misuse

The fake raft node hands out the Readys raft hands out in the finding's scenario, which `merged_snapshot_stale_term_test.go`
plays with five real `RawNode`s:

1. A follower's Ready at term 2, with member 2 as leader, the committed term-1 entry (index 2) and two term-1 `MsgSnap`s.
   raft emits these when the node stepped down during the stalled save: messages made while leader stay in `msgs`
   until the next Ready.
2. The commit of member 2's term-2 entry (index 3).
3. A leader's Ready at term 3 with a term-3 `MsgSnap` to member 3.

Ready 3 is there only as a sync point. Jobs run in order, and `sendMergedSnap` calls `SendSnapshot` within the job,
so once the message to 3 arrives, every earlier merged message has been sent. With the fix, Ready 3's message is
still sent, so the test also checks that the fix does not drop a current message. The assertion is the guarantee at
the receiver: member 5, a real raft node at term 1 that has applied index 1 (as raft has it when it lags behind the
leader's compacted log), steps the message as raft would on receipt, and its last log term must not exceed its
term. raft's own `MsgSnap`s always keep it, because a leader's snapshot is of its log, whose terms are at most its
term. etcd's server code uses only `Ready`'s documented fields.

## Why the fix works

At the base, `processMessages` queues every `MsgSnap` on `msgSnapC` (16 slots; `applyAll` is its only consumer).
Each `applyAll` job, after applying its batch and waiting for `notifyc`, takes at most one queued message and merges
it with `(appliedi, appliedt)`. Nothing ties the message's term to what was applied:

- In the scenario, job 1 takes member 4's message.
- Job 2 applies the term-2 entry and takes member 5's message, which is sent as term 1 with a term-2 snapshot.

With the fix, a job merges a queued message only if `appliedt <= m.Term`; job 2 drops member 5's message, and job 3
sends the term-3 message to member 3. That is exactly raft's own guarantee for a `MsgSnap` (raft#47's
`m.Term >= m.Snapshot.Metadata.Term`): a leader's snapshot is of its log, whose terms are at most its term. A member
at `m.Term` that installs the merged snapshot then never has a last log term above its own term, which is what the
gap-of-two panic needs.

Dropping is safe for liveness. `appliedt > m.Term` means an entry (or a received snapshot) of a term above `m.Term`
was committed and applied here, so raft had left `m.Term` before this job; every term change resets the progress of
every peer (`raft.reset`), so no leader waits for `m`'s `ReportSnapshot`. The current leader, this member or
another, probes the follower afresh and sends its own `MsgSnap` if the follower is behind its compacted log. The
base already drops a `MsgSnap` without a report when `msgSnapC` is full (`processMessages`).

What the fix does not exclude: the finding's second shape (data of `m.Term` or older, whose last entries were
committed by a later leader after this member stepped down) is still sent under `m.Term`. Its snapshot term is at
most `m.Term`, so the receiver's last log term stays at most its term; the data is committed, so the receiver's log
is a prefix of the committed log. No wrong result or panic follows (finding, "What the receiver can do afterwards").
The verified fork excludes it too, with the stronger check below, because its proof's invariant on `MsgSnap` says
"committed at `m.Term`"; upstream has no such invariant to keep.

## If a reviewer asks

Where the defect is: `applyAll` pairs a message raft made as leader of `m.Term` with data applied later, and
`createMergedSnapshotMessage` (its only caller is `applyAll`) keeps `m.Term`. raft's messages are consistent; the
pairing is etcd's. The candidate fixes, and why this one:

- **(chosen) Drop when `appliedt > m.Term`**, in `applyAll`: one condition on data the job already has, at the
  only place that pairs the two, and it states the invariant raft's `MsgSnap`s keep. Its drops are a subset of
  those of the next option, with the same liveness argument.
- **(a) Drop when raft's term changed** (the previous version of this branch, and the verified fork's de825d8c6
  with `==`): the raft goroutine records the latest `HardState.Term` and passes it in a new `toApply.raftTerm`;
  `applyAll` drops `m` if `m.Term < raftTerm`. Also correct, and stronger (it excludes the second shape), but it
  adds a field and raft-goroutine bookkeeping for a case with no upstream consequence. `>=`, not `==`: raft can run
  Readys ahead of the apply jobs, so job `k` can take a message made in a later Ready at a newer term, and `==`
  would drop it with no term change to reset the leader's progress (stuck in `StateSnapshot`). Leadership need not
  be checked besides the term: raft makes `MsgSnap` only as leader, and a check-quorum step-down at the same term
  leaves the log and commit index frozen until a higher term.
- **(b) Restamp `m.Term` with the current or applied term**: the sender need not be leader at that term (it is a
  follower in the scenario), so the message would claim a leadership it does not have.
- **(c) Snapshot at the message's term** (merge only data of term at most `m.Term`): the merged snapshot is the
  backend at `appliedi`; etcd cannot snapshot an older index. Dropping is the feasible form of (c), which is the
  chosen fix.
- **(d) Reject in raft** a `MsgSnap` whose snapshot term exceeds `m.Term` (raft#47's invariant; its check panics
  `appending out-of-order term` instead): raft's own messages never violate it, so the check would only turn
  etcd's bad message into a receiver panic or a silent drop. It is defense in depth for raft, not this fix.
- **Why not `s.Term()` or `s.isLeader()`**: `s.Term()` is the applied entry's term (`appliedt` itself, through
  `SetTerm`); `isLeader()` holds again after a re-election at a later term, and the message is made at `m.Term`
  either way.
- **Why not `s.r.Status()` in `applyAll`**: a round trip to raft's goroutine in every job that takes a message,
  for option (a)'s precision.
- **Mixed versions**: a member that installed a bad merged snapshot from an unfixed leader can have `appliedt`
  above its raft term; its own later `MsgSnap`s at a term below `appliedt` would then be dropped. Reaching that
  needs this bug first; not traced further.
- **Cost**: one comparison per queued `MsgSnap`.
- **Backport**: the release branches were not checked. The fix is self-contained.

## check.py

2026-10-23: no FAIL. WARNs kept:

- The fix's two-line comment stays: it says why a message is dropped (whose snapshot it would be, and that nothing
  waits for it), not what the condition does.
- The issue's prose (the invariant, a four-step scenario and its consequence, the panic) is what a maintainer needs
  in order to care.
- The PR's words hold two permalinks, the wrong assumption with its effect at the receiver, and one sentence of
  change with why dropping is safe.
