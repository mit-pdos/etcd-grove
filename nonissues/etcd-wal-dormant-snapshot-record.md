---
upstream: none
checked: 2026-11-11
links:
blocks-proof: no
---
# etcd: a crash between saving a received snapshot and its hard state leaves a WAL snapshot record that a later restart opens at

The raft loop persists a snapshot received from the leader as `SaveSnap` (synced) then `Save` of
the hard state and entries ([raft.go](https://github.com/etcd-io/etcd/blob/6974f522338b/server/etcdserver/raft.go#L249)). A crash between the two
(etcd's own `raftAfterSaveSnap` failpoint) leaves a snapshot record above the last saved commit.
The first restart ignores it (correctly: raft never acknowledged the snapshot). Once the restarted
member's commit passes its index, the next restart opens the WAL at that record: what a restart
reads depends on the whole WAL history across restarts, not on the last restart's read plus the
later writes. With a purge in between it can go the other way: the apply thread's own snapshot
`a` below the dormant record's index, `ReleaseLockTo(a)`
([wal.go](https://github.com/etcd-io/etcd/blob/6974f522338b/server/storage/wal/wal.go#L909)) and the purge delete the file holding the dormant
record (a file is named by its first entry, but may hold snapshot records above `a`), and the
restart then opens at `a`, not at the dormant record.

**Why not an issue:** raft-safe: the dormant record is a committed snapshot and the member's entry
at its index is the committed one, so either read is a compaction of the same durable log (raft's
`StorageHolds` allows a base above raft's). Behavior etcd does not promise otherwise; no fix
(decided by etcd-grove-81, 2026-11-11, D2). Shown with the WAL crash spec's harness (W0
`TestCW2Harness`) and robustness tester (W1.5, chain 3002; W3's targeted runs: RESULTS).

## Proof

no: the WAL crash spec (W4) states the reader over the whole history, and allows a missing prefix
up to the last released snapshot's record (`notes/decisions.md`, "WAL W3"); the `Save` law's
premise is restated over the restart's read (W1.5 §3.2).
