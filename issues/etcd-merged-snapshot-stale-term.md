---
upstream: none
checked: 2026-11-01
links:
  - etcd-io/etcd#7470 issue closed: a different bug in the same merge (the snapshot's term looked up in a possibly compacted raft log, a panic)
  - etcd-io/etcd#7513 pr merged: the fix of #7470 (the snapshot's term from `etcdProgress.appliedt`), the code this finding is about
  - etcd-io/raft#47 pr open: states the invariant broken here (`m.Term >= m.Snapshot.Metadata.Term` for a `MsgSnap`); does not fix etcd
  - etcd-io/raft#108 issue open: the same `need non-empty snapshot` panic, from `MemoryStorage.Snapshot` in a fuzzing harness; a different cause
blocks-proof: yes
---

# etcdserver: a leader that steps down while saving a Ready can send a follower a snapshot of a term above the follower's term

A leader that steps down while it is still saving a Ready (a slow disk) later sends the `MsgSnap`s it
made as leader with snapshot data it applied afterwards, keeping the message's old term. A follower
still at that old term installs it, and its log then ends at a term above its own current term,
which Raft rules out. With a gap of two terms, a leader of the term in between can then panic with
`need non-empty snapshot`.

**Expected:** a `MsgSnap` of term `T` should carry a snapshot of term at most `T`, as raft's own
`MsgSnap`s do (a leader's snapshot is of its own log; etcd-io/raft#47 states this invariant), so
that no member's last log term exceeds its current term.

**Impact:** needs a leader whose save of a Ready stalls for longer than an election timeout, at
least two followers behind its compacted raft log (so 5 or more members), and a partition that
keeps one of them at the old term; the panic additionally needs a gap of two terms and the
in-between leader still up and without a snapshot. No wrong commit was found. Rare, but every
release since #7513 (2017) has the code.

**Reproduction:** `TestMergedSnapshotTerm` in
[`issues/etcd-merged-snapshot-stale-term/merged_snapshot_term_test.go`](etcd-merged-snapshot-stale-term/merged_snapshot_term_test.go),
copied into `server/etcdserver` at etcd-io/etcd@1573d59416efa220421c451f5266b24a5d8374ef
(2026-10-28), go1.27.3 linux/amd64. It runs the real raft loop and apply loop of member 1 (the
harness of `TestSnapshotOrdering`) fed the Readys raft hands out in the scenario, and delivers the
merged `MsgSnap` to member 5, a real `raft.Node` at term 1:

```
$ go test ./etcdserver -run TestMergedSnapshotTerm -count=1
    logger.go:146: 2026-11-01T04:09:20.822Z	INFO	5 became follower at term 1
    logger.go:146: 2026-11-01T04:09:20.823Z	INFO	5 [commit: 3, lastindex: 3, lastterm: 2] restored snapshot [index: 3, term: 2]
--- FAIL: TestMergedSnapshotTerm (0.01s)
        	Error:      	"2" is not less than or equal to "1"
        	Messages:   	last log term of member 5, at term 1, after it installs the MsgSnap
FAIL	go.etcd.io/etcd/server/v3/etcdserver	0.042s
```

The same directory has two raft-level tests (package `raft`, written against raft v3.7.0's
pointer API): `merged_snapshot_stale_term_test.go` plays the whole scenario with five real
`RawNode`s and etcd's pipeline emulated (the stalled save, the step-down inside it), and
`stale_term_gap2_ack_test.go` the gap-of-two panic from member 5's state with hand-built messages.
Both pass when the bug is present.

**Cause:** raft stamps a `MsgSnap` with the leader's term when it makes it.
[`processMessages`](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/server/etcdserver/raft.go#L374-L385)
queues it on `msgSnapC`, and a later apply job in
[`applyAll`](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/server/etcdserver/server.go#L994-L998)
takes it and replaces only its snapshot with the data applied so far
([`createMergedSnapshotMessage`](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/server/etcdserver/snapshot_merge.go#L32-L53)),
keeping `m.Term`. If raft stepped down before that job, the applied data can be of a newer term.

## Proof

yes: the verified fork carries a fix (`goose-lean` `de825d8c6`, `etc/goose.py`: the merge only at
the message's term), which the snapshot track's `.snap` message clause needs (content committed at
`m.Term`; `notes/decisions.md`, D22a). Since 2026-10-31 the fork's merge also has a proof-only guard
(the message's snapshot index at most `ep.appliedi`, `goose-lean-snapguard` `633036387`;
`notes/decisions.md`, "The merged snapshot's index guard"), not a fix of this issue.

## Fix

**Branch**: `fix/etcd-merged-snapshot-stale-term` in `~/etcd-fixes/etcd-merged-snapshot-stale-term` (upamanyus/etcd, not pushed): 1645e3a35 test, 4a88c8a8e fix
**Base**: etcd-io/etcd@3aaab3479b6c4f5fe1b2b8f33437093c2caae88a

**PR draft**:

Title: etcdserver: drop a queued MsgSnap older than the applied term

raft makes a `MsgSnap` as leader of the message's term. [`processMessages`](https://github.com/etcd-io/etcd/blob/3aaab3479b6c4f5fe1b2b8f33437093c2caae88a/server/etcdserver/raft.go#L374-L385) queues it, and a later apply job in [`applyAll`](https://github.com/etcd-io/etcd/blob/3aaab3479b6c4f5fe1b2b8f33437093c2caae88a/server/etcdserver/server.go#L992-L998) replaces its snapshot with the data applied so far but keeps the message's term. When raft steps down before the job runs, that data can be of a newer term, and a follower still at the message's term that installs it has a log term above its current term. This PR drops a queued `MsgSnap` older than the last applied entry's term: raft has then left that term and reset every peer's progress, so no leader waits for the message.

The first commit adds a test of the issue's example, which fails on `main`; the second, the fix, makes it pass.

A reviewer may ask why not restamp `m.Term` (the sender need not be leader at the newer term) or
check raft's current term (`>=`, not `==`, since raft runs Readys ahead of the apply jobs; stronger
but needs a new field). The fork uses the stronger check; upstream has no invariant the weaker one
leaves broken.

## Notes

Untraced consequence: restarting such a follower with `--force-new-cluster` appends forced
conf-change entries stamped with its (older) WAL term after the snapshot, so its log terms go
down. The 2026-10-23 review's plan was "upstream, leading with the Raft invariant", which the report
follows.
