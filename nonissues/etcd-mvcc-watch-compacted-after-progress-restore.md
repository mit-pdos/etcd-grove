---
upstream: none
checked: 2026-11-09
links: []
blocks-proof: no
---

# mvcc: after a snapshot restore, a watch told by a progress notification that nothing changed up to revision P is cancelled as compacted at a revision at or below P

A watcher whose key does not change keeps the `minRev` it registered with: a progress
notification (`RequestProgress`, or the stream-wide one) does not raise it. When the member then
restores a snapshot (`applySnapshot` → `mvcc`'s `Restore`) whose store is compacted at a revision
`C` above that `minRev` but at or below the progress revision `P`, the next resync sends the watcher
a compaction response at `C`: the client's watch ends with `ErrCompacted` at a revision it was
already told it had seen everything up to. A client that relies on progress notifications to resume
(Kubernetes' watch cache, which requests them) relists although no event was lost.

**Why not an issue:** the test reproduces it at mvcc's API (a watch stream of the store, a
`Restore` onto a later, compacted backend), not through a running cluster: reaching it through
etcd needs a lagging follower that receives a snapshot taken after a compaction, while a client
watches it with progress notifications. No safety property breaks (the watch ends; it does not
skip an event): an unnecessary cancellation. Move it to `issues/` with an integration test through
a follower's snapshot.

## Proof

no: 3f's watch guarantee (`Spec/go_etcd_io/etcd/server/v3/storage/mvcc/ApiWatch.lean`, `wStep`)
states a compaction response against the watcher's **events** position (`posEvOf`: its last
event's revision, which the store's `minRev` bounds), not its position after progress responses
(round 1 of 3f's review, F1); 1b's `watchStep` is weakened the same way.

## Notes

`TestWatchCompactedAfterProgressRestore` in
[`nonissues/etcd-mvcc-watch-compacted-after-progress-restore/watch_compacted_after_progress_restore_test.go`](etcd-mvcc-watch-compacted-after-progress-restore/watch_compacted_after_progress_restore_test.go)
(package `mvcc_test`; copied into `server/storage/mvcc`, or into any package importing the server's
`mvcc`) fails at the pinned fork (upamanyus/etcd@a4d2bb1720b9, server/v3, go1.27), run as a copy in
`examples/specreq/mvccwatch` (2026-11-09):

```
=== RUN   TestWatchCompactedAfterProgressRestore
    zz_tmp_test.go:73: watcher told nothing changed up to 21 is cancelled as compacted at 10
--- FAIL: TestWatchCompactedAfterProgressRestore (0.11s)
```

Where: `watchable_store.go` `progressIfSync` (sends the progress, `minRev` untouched), `Restore`
(synced watchers moved to `unsynced` with their `minRev`), `watcher_group.go` `chooseAll`
(`w.minRev < compactRev` sends the compaction). A fix: raise a synced watcher's `minRev` to the
progress revision + 1 when a progress is sent (it has no event up to there).
