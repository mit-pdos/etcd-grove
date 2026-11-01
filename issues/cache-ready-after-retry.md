---
upstream: reported
checked: 2026-11-01
links:
  - etcd-io/etcd#22614 issue open: this bug, reported 2026-10-19
  - etcd-io/etcd#22618 pr open: a fix by someone else (NUAAwqy), our branch's fix and test verbatim, "Fixes #22614"; needs-ok-to-test, no review
  - etcd-io/etcd#22408 pr open: related, not this bug (the same retry loop: back-off and GetTimeout never read)
  - etcd-io/etcd#21536 issue closed: related, not this bug (Get(WithRev) with revision gaps; fixed by #21540)
  - etcd-io/etcd#20691 pr merged: related (made the demux keep a min/max revision range, where Init's purge comes from)
blocks-proof: yes
---

# cache: the cache never becomes ready again after a compaction cancels its upstream watch

When the cache's upstream watch fails (a compaction cancels it, for one) and the cache retries from a
fresh `Get` at a revision that does not continue what it had seen, the retried watch's first response
purges the cache's demux, which stops the store watcher just registered for it; the loop goes around
with its `sync.Once` spent, so `Ready()` stays false, `WaitReady` never returns and `Cache.Watch`
blocks, while the store keeps up to date.

**Reproduction:** `TestCacheReadyAfterCompactionResync` in
[`issues/cache-ready-after-retry/cache_ready_after_retry_test.go`](cache-ready-after-retry/cache_ready_after_retry_test.go),
copied into `cache` at etcd-io/etcd@1573d59416efa220421c451f5266b24a5d8374ef (2026-10-28), go1.27.3
linux/amd64 (it uses `cache_test.go`'s mock watcher and KV stub):

```
$ go test . -run '^TestCacheReadyAfterCompactionResync$' -count=1
getWatch failed, will retry after 50ms: etcdserver: mvcc: required revision has been compacted
--- FAIL: TestCacheReadyAfterCompactionResync (0.00s)
    cache_ready_after_retry_test.go:58: cache not ready after the resync
FAIL
```

## Proof

yes: the verified fork carries the fix (`64313a1f8`, fork branch `cache-ready-after-retry`); the bug
itself is liveness (readiness never set), which the cache's safety specs do not state.

## Fix

**Branch**: `fix/cache-ready-after-retry` in `~/etcd-fixes/cache-ready-after-retry` (upamanyus/etcd, pushed): 4c9743e0e test, 27352098d fix
**Base**: etcd-io/etcd@22cc5d9acd4a5953dfdfc2594dbeb53da89bb0d4

## Notes

#22618 carries this branch's diff; we have not opened a PR of our own.
