---
upstream: none
checked: 2026-11-11
links:
  - etcd-io/etcd#19095 pr merged: ReadAll returns the continuous entries with ErrSliceOutOfRange (for the robustness test's WAL reader); the same error, a different cause, bootstrap still exits on it
  - etcd-io/etcd#19674 issue closed: robustness flake reading a WAL; not this bug
blocks-proof: no
---
# etcdserver: a follower killed while persisting a received snapshot cannot restart

A follower that is killed (or loses power) while it persists a raft update holding both a snapshot
received from the leader and log entries after it can be left unable to restart: every start
exits with `failed to read WAL, cannot be repaired ... wal: slice bounds out of range`. The WAL
then holds the snapshot record and the new entries, but not the hard state saved after them.

**Expected:** a member should restart from whatever a crash leaves of its WAL, as the WAL's
torn-write recovery (`Repair`) and raftNode's "save the snapshot first" ordering
([raft.go](https://github.com/etcd-io/etcd/blob/6974f522338b7dc67575080f07285e5b4348d47d/server/etcdserver/raft.go#L245-L253))
intend.

**Impact:** a follower catching up through a snapshot (a slow member, or one restarted after the
leader compacted its log), default configuration. The raft update must carry entries after the
snapshot: the leader's next append reached the follower before its raft loop took the update, as
happens when the loop is still busy with an earlier update (a slow fsync). Under kill -9 the
window is inside that update's `Save` when its entries exceed the WAL's 128 KiB write buffer;
under power loss, whenever the entries and the hard state are in different disk sectors. The
member stays down until an operator removes its data directory and adds it back. Seen at
v3.7.3 and main; every release with the WAL's `ErrSliceOutOfRange` check (v3.6+); before it, the
restart panics instead.

**Reproduction:** `TestReceivedSnapshotSaveCrashBlocksRestart` in
[`issues/etcd-wal-received-snapshot-save-crash-no-restart/received_snapshot_crash_test.go`](etcd-wal-received-snapshot-save-crash-no-restart/received_snapshot_crash_test.go),
copied into `server/storage/wal` at etcd-io/etcd@6974f522338b7dc67575080f07285e5b4348d47d
(2026-11-10), go1.27.1:

```
$ go test ./storage/wal -run TestReceivedSnapshotSaveCrashBlocksRestart
--- FAIL: TestReceivedSnapshotSaveCrashBlocksRestart (0.12s)
    received_snapshot_crash_test.go:97: restart after a crash in the Save following a received snapshot fails (bootstrap Fatals): open at snapshot 0: wal: slice bounds out of range, snapshot[Index: 0, Term: 0], current entry[Index: 11, Term: 2], len(ents): 3
FAIL
```

The test makes the WAL calls raftNode makes for such an update (`SaveSnapshot`, then `Save` of the
hard state and 200 KiB of entries) and then cuts the file as the kill leaves it (the entries
written, the hard state record still in the write buffer), then reads it as bootstrap does.
`TestFollowerReadySnapshotAndEntries`
([`follower_ready_snapshot_entries_test.go`](etcd-wal-received-snapshot-save-crash-no-restart/follower_ready_snapshot_entries_test.go),
copied into etcd-io/raft@c51f010c851edd0dada5af41bafbf68e54617767, passes) shows raft producing such an update:
a follower that has not yet advanced its last `Ready` steps the leader's `MsgSnap(10)` and
`MsgApp(prev 10, entries 11..12)`; its next `Ready` has the snapshot, the hard state and entries
11..12.

End to end, [`e2e.sh`](etcd-wal-received-snapshot-save-crash-no-restart/e2e.sh) runs a
three-member cluster of etcd at the same commit built with failpoints (`gofail enable
server/etcdserver/ server/etcdserver/api/snap/ server/storage/wal/`), restarts a stopped member
so that the leader sends it a snapshot, uses failpoint sleeps to make the snapshot and the next
append land in one update, and kills the member (kill -9) while its `Save` waits before the fsync
(`walBeforeSync`). The member never restarts
([`e2e-output.txt`](etcd-wal-received-snapshot-save-crash-no-restart/e2e-output.txt)):

```
{"level":"fatal","caller":"etcdserver/bootstrap.go:686","msg":"failed to read WAL, cannot be repaired",
 "error":"wal: slice bounds out of range, snapshot[Index: 0, Term: 0], current entry[Index: 85, Term: 2], len(ents): 9"}
```

**Cause:** raftNode saves the update as `SaveSnap(s)` then `Save(hardState, entries)`
([raft.go](https://github.com/etcd-io/etcd/blob/6974f522338b7dc67575080f07285e5b4348d47d/server/etcdserver/raft.go#L247-L259)).
`Save` encodes the entries before the hard state
([wal.go](https://github.com/etcd-io/etcd/blob/6974f522338b7dc67575080f07285e5b4348d47d/server/storage/wal/wal.go#L1017-L1025)),
so a crash can keep the entries and lose the hard state, whose commit is `>= s`. On restart,
`ValidSnapshotEntries` keeps only the snapshot records at or below the last saved commit, so `s`
is dropped and the WAL is opened at an older snapshot; `ReadAll` then meets entries `s+1..` past
the end of the older log and returns `ErrSliceOutOfRange`, which `openWALFromSnapshot` treats as
fatal
([bootstrap.go](https://github.com/etcd-io/etcd/blob/6974f522338b7dc67575080f07285e5b4348d47d/server/etcdserver/bootstrap.go#L683-L687)).

## Proof

no: liveness only (the restart exits); the WAL spec's reader returns no state on such an image,
and the restart contract allows bootstrap not to return.

## Fix

Not drafted. Options: write the snapshot's hard state (commit `>= s`) with the snapshot record in
`SaveSnap` (or have raftNode save the hard state before the entries of such an update), or let
`ValidSnapshotEntries` keep a snapshot record that entries above it follow.

## Notes

A gofail `panic` at `walBeforeSync` does not reproduce it: the panic runs raftNode's deferred
`storage.Close`, which flushes and syncs the WAL. A kill -9 (or power loss) is needed, hence the
sleep and the external kill in `e2e.sh`. etcd's `tests/e2e` could not be built offline
(missing modules such as `github.com/creack/pty`), so the end-to-end reproduction is a script over
the failpoint-enabled binaries rather than an e2e test.
