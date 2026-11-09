---
upstream: none
checked: 2026-11-03
links:
  - etcd-io/etcd#20693 pr merged: related; the gRPC watch rejects a negative start revision (it broke the resync); mvcc's documentation and code left as they were
blocks-proof: no
---

# mvcc: WatchStream.Watch with a negative start revision does not watch "after currentRev" as documented

`WatchStream.Watch`'s documentation says "If "startRev" <=0, watch observes events after
currentRev", but only `0` is treated so: a start revision of `-1` replays the history from the
beginning, and one of `-2` or below gets a compaction response with compact revision `-1` on a store
never compacted (or at the compaction revision on a compacted one).

**Why not an issue:** documentation only: etcd's gRPC watch rejects a negative start revision
([watch.go#L270](https://github.com/etcd-io/etcd/blob/4b0b745025716b893c64dbee443e3f969931a16b/server/etcdserver/api/v3rpc/watch.go#L270),
since #20693), so no etcd caller passes one; only a Go user of mvcc does.

## Proof

no: `WatchStream.Watch.contract` takes `0 ≤ startRev` (`Spec/go_etcd_io/etcd/server/v3/storage/mvcc/Api.lean`),
which the gRPC layer's check gives etcd's server.

## Notes

`TestWatchNegativeStartRev` in
[`nonissues/etcd-mvcc-watch-negative-start-rev/watch_negative_start_rev_test.go`](etcd-mvcc-watch-negative-start-rev/watch_negative_start_rev_test.go)
(copied as `zz_watch_negative_start_rev_test.go` into `server/storage/mvcc`) checks the documented
behavior; it fails at etcd-io/etcd@4b0b745025716b893c64dbee443e3f969931a16b (2026-11-03, go1.27.3):

```
$ (cd server && go test ./storage/mvcc -run '^TestWatchNegativeStartRev$' -count=1)
--- FAIL: TestWatchNegativeStartRev (0.62s)
    --- FAIL: TestWatchNegativeStartRev/startRev=-1 (0.00s)
        zz_watch_negative_start_rev_test.go:47: before any later write: 1 events, revision 2, compact revision 0; want nothing
    --- FAIL: TestWatchNegativeStartRev/startRev=-2 (0.11s)
        zz_watch_negative_start_rev_test.go:47: before any later write: 0 events, revision 0, compact revision -1; want nothing
FAIL
```

Where: [watcher.go#L45](https://github.com/etcd-io/etcd/blob/4b0b745025716b893c64dbee443e3f969931a16b/server/storage/mvcc/watcher.go#L45)
(the documentation) and
[watchable_store.go#L141](https://github.com/etcd-io/etcd/blob/4b0b745025716b893c64dbee443e3f969931a16b/server/storage/mvcc/watchable_store.go#L141)
(`synced := startRev > s.store.currentRev || startRev == 0`). A fix: document `startRev == 0` (and a
negative start revision as invalid), or treat `startRev < 0` as `0`.
