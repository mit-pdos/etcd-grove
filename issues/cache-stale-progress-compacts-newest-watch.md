---
upstream: none
checked: 2026-11-01
links:
  - etcd-io/etcd#15237 pr merged: progress responses go through mvcc's watch channel, but a watch's created response can still overtake a queued progress response (issues/etcd-watch-progress-before-created.md), the trigger reproduced here
  - etcd-io/etcd#20221 issue closed: same symptom on the server side (a lagging member sent progress below a watch's start revision); not the cache's missing check
  - etcd-io/etcd#20229 pr merged: the server fix of #20221's trigger; does not cover a progress computed before the watch existed
  - etcd-io/etcd#20614 pr merged: related (made the demux progress-aware); no handling of a progress below the cache's start
blocks-proof: yes
---

# cache: a stale progress notification makes a watch "from now" fail with ErrCompacted

A `cache.Cache` whose upstream watch receives, right after it is created, a progress notification
below the revision the cache was loaded at, cancels the next `Cache.Watch` without a revision ("from
now") with `ErrCompacted` as soon as an event arrives, instead of delivering the event. The stale
progress comes from a `RequestProgress` on the same client while the cache (re)creates its watch.

**Expected:** a `Cache.Watch` with no revision should start at the cache's latest revision and
receive the events after it; a progress notification below what the cache was loaded at says nothing
new and should not move the cache's view of "now" backwards.

**Impact:** users of `go.etcd.io/etcd/cache/v3` whose client also requests progress (the cache's own
progress requestor does, when a cache read waits for a revision; any other `RequestProgress` on the
same client), on a busy watch stream; the trigger is
[etcd-watch-progress-before-created](etcd-watch-progress-before-created.md) (a member never sends a
progress below a watch's start otherwise since #20229). The watch fails with a spurious compaction
error; a caller that retries from the reported revision recovers. One member suffices.

**Reproduction:** `TestCacheStaleProgressCompactsNewestWatch` in
[`issues/cache-stale-progress-compacts-newest-watch/cache_stale_progress_test.go`](cache-stale-progress-compacts-newest-watch/cache_stale_progress_test.go),
copied into `tests/integration` at etcd-io/etcd@1573d59416efa220421c451f5266b24a5d8374ef
(2026-10-28), go1.27.3 linux/amd64. One member, eight busy watches and a txn writer on the client's
shared stream; per trial, another goroutine calls `RequestProgress` until the cache's `Get` starts,
then `cache.New`, `WaitReady`, `Watch(prefix+"x")` with no revision, and a put of `prefix+"x"`; up to
500 trials.

```
$ go test ./integration/ -run '^TestCacheStaleProgressCompactsNewestWatch$' -count=1
--- FAIL: TestCacheStaleProgressCompactsNewestWatch (19.12s)
    cache_stale_progress_test.go:112: trial 100: a cache watch from now was canceled (compact revision 830, "etcdserver: mvcc: required revision has been compacted")
    cache_stale_progress_test.go:122: trial 100: the cache's watch (from 831, after its Get at 830) received a progress notification at 829
    cache_stale_progress_test.go:127: 1 of 101 trials: a stale progress notification compacted a cache watch from now
FAIL
```

**Cause:** the cache loads at revision `R` and initializes its demux at `R + 1` with no latest
revision yet
([`Init`](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/cache/demux.go#L119-L143)).
`Broadcast` checks a progress notification only against the latest revision, which is 0, so a
progress at `P < R` is accepted as the latest
([L145-L158](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/cache/demux.go#L145-L158)).
A watch "from now" then registers at `P + 1`
([`Register`](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/cache/demux.go#L97-L100)),
below the demux's minimum `R + 1`, and is canceled as compacted when the next events arrive.

## Proof

yes: the cache's watch contract needs every progress notification at or above the watch's position
(`Proof/go_etcd_io/etcd/cache/v3/InvEtcd.lean`), which holds only over the verified fork's server
ordering fix (`09669450f`, the fix of etcd-watch-progress-before-created).

## Fix

`Broadcast` should check a progress notification against `max(maxRev, minRev - 1)` (or `Init` set
the latest revision to `minRev - 1`); not tried upstream.

## Notes

The user's 2026-10 review: a non-issue if the client guarantees no stale progress, to revisit if a
failing end-to-end test exists. It does (above): neither the client nor the server rules it out at
`main`. Fixing the server ordering alone also closes it; kept as its own file because the demux's
missing check is a second root cause. A demux-level test (`Init(11)`, `Broadcast` of a progress at 5,
`Register(w, 0)`, an event at 11) fails deterministically with "a watch from now was compacted at 6"
(2026-10-17).
