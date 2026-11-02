---
upstream: known
checked: 2026-11-02
links:
  - etcd-io/etcd#22294 issue open: this bug (by martin-k-m, 2026-08-16)
  - etcd-io/etcd#22295 pr open: its fix (remove compacted watchers from the unsynced group when capped)
  - etcd-io/etcd#21174 pr closed: an earlier fix of the same leak, not merged
  - etcd-io/etcd#21189 pr closed: related (choose's other branch, the group modified while iterated)
blocks-proof: no
---

# mvcc: with more than 512 unsynced watchers, a compacted watcher is sent the compaction response again at every sync

When more than 512 watchers (`maxWatchersPerSync`) are unsynced at once and some of them start
below the compaction revision, those chosen through the sync loop's copy of the unsynced group are
sent their compaction response but stay in the unsynced group, so every later sync (every 100 ms)
sends it again, until the client cancels the watch. With 512 or fewer unsynced watchers each is
sent it once.

**Reproduction:** `TestWatchCompactedResentManyUnsynced` in
[`issues/etcd-watch-compacted-resent/watch_compacted_resent_test.go`](etcd-watch-compacted-resent/watch_compacted_resent_test.go),
copied into `server/storage/mvcc` at etcd-io/etcd@a2e3642bcd2cca3a802503cdb09f64a3dc15cdf5
(2026-11-02), go1.27.3 (600 watch streams of one watch each, from revision 1 after a compaction at
4, then one second of the store's own sync loop):

```
$ (cd server && go test ./storage/mvcc -run '^TestWatchCompactedResentManyUnsynced$' -count=1)
--- FAIL: TestWatchCompactedResentManyUnsynced (1.03s)
    watch_compacted_resent_test.go:55: 4608 compaction responses for 600 compacted watches, want one each
FAIL
```

## Proof

no: `watcherGroup.choose.spec` states the code's behavior, the compacted members deleted from the
copy only (`Spec/go_etcd_io/etcd/server/v3/storage/mvcc/watcherGroup__choose.lean`); the watch
specs across a compaction are still drafts (`notes/watch-compaction-plan.md`).
