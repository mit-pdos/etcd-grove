---
upstream: none
checked: 2026-11-09
links:
  - etcd-io/etcd#20262 issue closed: related, not this bug: asks for progress notifications to watchers before a compaction
blocks-proof: no
---
# watch: after a follower restores a snapshot, a watch told by a progress notification that it is current at revision P is cancelled as compacted at P

A watch on a follower whose key does not change, after a progress notification (`RequestProgress`)
at revision P, is cancelled with `ErrCompacted` at compact revision P when the follower catches up
from a leader snapshot taken after a compaction at P, although the watch has seen everything up to P
and needs nothing below P+1. A client that resumes from progress notifications (Kubernetes' watch
cache requests them) has to relist although no event was lost.

**Expected:** a watch should be cancelled as compacted only when a revision it still needs is
compacted; after a progress notification at P it needs only revisions above P, as
[`rpc.proto`](https://github.com/etcd-io/etcd/blob/d622ec57cf46c119f1a550343c34b26327cead0f/api/etcdserverpb/rpc.proto#L791-L795)
describes them: useful "when clients wish to recover a disconnected watcher starting from a recent
known revision".

**Impact:** clusters with a member far enough behind to be sent a snapshot (a partition or a slow
member, then a compaction and enough writes to compact the leader's raft log) and clients watching
through that member with progress notifications; the watch ends and the client relists. No event
is lost. Default configuration; three members.

**Reproduction:** `TestV3WatchProgressThenRestoreSnapshotCompacted` in
[`issues/etcd-mvcc-watch-compacted-after-progress-restore/watch_progress_restore_test.go`](etcd-mvcc-watch-compacted-after-progress-restore/watch_progress_restore_test.go)
(a watch on member 0, a progress request, member 0 partitioned while the others compact at the
progress revision and take snapshots, then healed), copied into `tests/integration/clientv3/watch`
at etcd-io/etcd@d622ec57cf46 (2026-11-06), go1.27.3 (also fails at the verified fork's
a4d2bb1720b9):

```
$ go test ./integration/clientv3/watch -run '^TestV3WatchProgressThenRestoreSnapshotCompacted$' -count=1
--- FAIL: TestV3WatchProgressThenRestoreSnapshotCompacted (1.46s)
    watch_progress_restore_test.go:68: progress notification at revision 6
        	Error:      	Should be false
        	Messages:   	watcher told nothing changed up to 6 is cancelled as compacted at 6
FAIL
```

**Cause:** a progress notification
([`progressIfSync`](https://github.com/etcd-io/etcd/blob/d622ec57cf46c119f1a550343c34b26327cead0f/server/storage/mvcc/watchable_store.go#L517-L545))
leaves the watcher's `minRev` at the revision it registered with.
[`Restore`](https://github.com/etcd-io/etcd/blob/d622ec57cf46c119f1a550343c34b26327cead0f/server/storage/mvcc/watchable_store.go#L207-L221)
moves synced watchers to the unsynced group with that `minRev`, and the next sync's
[`chooseAll`](https://github.com/etcd-io/etcd/blob/d622ec57cf46c119f1a550343c34b26327cead0f/server/storage/mvcc/watcher_group.go#L241-L270)
sends a compaction response to every watcher with `minRev` below the restored store's compact
revision.

## Proof

no: 3f's watch guarantee (`Spec/go_etcd_io/etcd/server/v3/storage/mvcc/ApiWatch.lean`, `wStep`)
states a compaction response against the watcher's **events** position (`posEvOf`: its last
event's revision, which the store's `minRev` bounds), not its position after progress responses
(round 1 of 3f's review, F1); 1b's `watchStep` is weakened the same way.

## Fix

Not written: when a progress notification is sent to a synced watcher, raise its `minRev` to the
progress revision + 1 (it has no event up to there).

## Notes

The same at mvcc's API (a watch stream of the store, a `Restore` onto a later, compacted backend):
`TestWatchCompactedAfterProgressRestore` in
[`watch_compacted_after_progress_restore_test.go`](etcd-mvcc-watch-compacted-after-progress-restore/watch_compacted_after_progress_restore_test.go)
(package `mvcc_test`, copied into `server/storage/mvcc`), which fails at the fork.
