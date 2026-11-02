---
upstream: unchecked
checked: 2026-11-01
links: []
---

# `Cache.Watch` concurrent with `Cache.Close` can panic in `sync.WaitGroup`, or outlive `Close`

- **Status**: an unstated precondition (a reachable panic when it is broken): `Watch` must not run
  concurrently with `Close`, which neither documents. Found by reading, not reproduced.
- **Where**: `cache/cache.go` at the fork's pin (`upamanyus/etcd` `633036387`): `Watch` (116-145;
  `c.waitGroup.Add(1)` at 142, after `WaitReady` and `demux.Register`), `Close` (307-310:
  `c.stop()` then `c.waitGroup.Wait()`, documented "cancels the private context and blocks until all
  goroutines return"). Go 1.27's `sync/waitgroup.go`: `Add` (117-133), `Wait` (200-215); its doc:
  "calls with a positive delta that occur when the counter is zero must happen before a Wait".
- **What happens**: `Close` cancels the cache's context, so the resync loop, the watch loop and the
  watchers' goroutines return and the counter falls to zero while `Close` waits. A `Watch` whose
  `WaitReady` passed (the cache was ready) still runs `Add(1)`:
  - between the last `Done` (counter 0, a waiter registered) and its reset of the state:
    `Add` panics, "sync: WaitGroup misuse: Add called concurrently with Wait";
  - after the reset, before the waiter returns from its semaphore: the waiter panics, "sync:
    WaitGroup is reused before previous Wait has returned";
  - after `Wait` returned: no panic, but `Close` has returned while the new watcher's goroutine
    runs, contrary to its comment.
- **Expected**: either `Close` documents that no `Watch` may run concurrently with or after it,
  or `Watch` refuses after `Close` (e.g. a closed flag checked under a lock that `Close` takes
  before `Wait`, with `Add` under the same lock).
- **How the proof handles it**: the "open" token `cacheOpen` (`Proof/go_etcd_io/etcd/cache/v3/
  InvCache.lean`, `cacheWgInv`): `Watch` takes a fraction of it, `Close` the whole, so a verified
  caller never overlaps them. `notes/decisions.md`'s entry on the cache's wait group called this
  conservatism ("Go's own implementation would not panic here"); that was wrong (corrected there,
  2026-11-01).
- **Possible fixes**: a mutex-guarded `closed` flag set by `Close` before `Wait` and checked by
  `Watch` around its `Add(1)` (returning a closed channel after `Close`); or documentation.
- **Found**: 2026-11-01, bounds plan B3's wait-group inventory (`notes/bounds-waitgroups.md`).
