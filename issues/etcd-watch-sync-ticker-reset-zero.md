---
upstream: known
checked: 2026-10-26
links:
  - etcd-io/etcd#22296 issue open: same bug (time.Since zero on Windows' coarse monotonic clock, Ticker.Reset panics); no maintainer response
  - etcd-io/etcd#22297 pr open: same bug, fix (`resyncDelay`); comments question the impact and prefer a clamp; cherry-picked into the fork as 5615016f6 (D19l)
---

# server/storage/mvcc: `syncWatchersLoop` resets its ticker with a zero duration, a panic

- **Status**: a bug (a reachable panic on a coarse monotonic clock). **Fixed in the fork**
  (D19l, 2026-10-18): etcd-io/etcd#22297 cherry-picked with its test (`TestResyncDelay`) onto
  `upamanyus/etcd` `goose-lean` as `5615016f6` (etc/goose.py's etcd pin since then).
- **Where**: `server/storage/mvcc/watchable_store.go` at bc8b52a50 (`etc/goose.py`'s etcd pin),
  `watchableStore.syncWatchersLoop` (`watchable_store.go:224-258`): after a sync pass it takes
  `syncDuration := time.Since(st)` (line 240) and, when the pass made progress but left watchers
  unsynced (`unsyncedWatchers != 0 && lastUnsyncedWatchers > unsyncedWatchers`, line 245), calls
  `delayTicker.Reset(syncDuration)` (line 246). Go's `time.Ticker.Reset` documents that "the
  duration d must be greater than zero; if not, Reset will panic" (`time/tick.go:63-66`).
- **What happens**: `time.Since(st)` is `0` whenever the monotonic clock did not advance between
  the two `time.Now()` calls. On Linux the monotonic clock has nanosecond resolution and a sync
  pass reads the backend, so the difference is practically never zero; on Windows the runtime's
  monotonic clock advances in coarse steps (the interrupt time, 0.5–15.6 ms), so a pass that
  finishes within one step returns `0`, and the loop panics with "non-positive interval for
  Ticker.Reset", killing the member. The branch is taken under load: a pass syncs at most
  `maxWatchersPerSync` (512) watchers, so with more unsynced watchers than that (or victims that
  stay unsynced) every pass satisfies the condition.
- **How it happens**: after each pass over unsynced watchers, `syncWatchersLoop` re-arms its
  ticker with the time the pass took, to yield to other store work. Go's `Ticker.Reset` panics
  on a non-positive duration, and `time.Since` is zero when the monotonic clock did not advance
  during the pass:

  1. The store has 1000 unsynced watchers (more than `maxWatchersPerSync`, 512).
  2. A pass records `st := time.Now()` and `lastUnsyncedWatchers = 1000`, then syncs 512
     watchers: `unsyncedWatchers = 488`.
  3. On a platform with a coarse monotonic clock, the pass finishes within one clock step:
     `syncDuration := time.Since(st)` is `0`.
  4. The pass made progress and left watchers unsynced (`488 != 0 && 1000 > 488`), so the loop
     calls `delayTicker.Reset(0)`, which panics with "non-positive interval for Ticker.Reset".

  ```go
  // server/storage/mvcc/watchable_store.go:240-247 (etcd main f061acd09)
  		syncDuration := time.Since(st) // <-

  		delayTicker.Reset(watchResyncPeriod)
  		// more work pending?
  		if unsyncedWatchers != 0 && lastUnsyncedWatchers > unsyncedWatchers {
  			// be fair to other store operations by yielding time taken
  			delayTicker.Reset(syncDuration) // <-
  		}
  ```

  ```go
  // time/tick.go:63-69 (Go 1.27.1)
  // Reset stops a ticker and resets its period to the specified duration.
  // The next tick will arrive after the new period elapses. The duration d
  // must be greater than zero; if not, Reset will panic.
  func (t *Ticker) Reset(d Duration) {
  	if d <= 0 { // <-
  		panic("non-positive interval for Ticker.Reset")
  	}
  ```
- **Expected**: the loop re-arms the ticker with the sync duration, or the default period when
  the duration is not usable; a zero duration is a valid reading of a clock.
- **How the proof handles it**: `Spec/time/Ticker__Reset.lean` requires a positive duration (as
  Go documents). Until D19l a local axiom (`Spec/time/Since.lean`) assumed `time.Since` returns a
  positive duration, which made `watchableStore.syncWatchersLoop` provable at the upstream code;
  without it the call is not provable, which is how the finding surfaced. Since D19l the proof is
  of the fork's fixed code: `resyncDelay` (`Proof/go_etcd_io/etcd/server/v3/storage/mvcc/
  resyncDelay.lean`) returns a positive duration for any `syncDuration`, the loop uses Perennial's
  `time.wp_Since` (any duration), and the local axiom is gone.
- **Possible fixes**: `if syncDuration > 0 { delayTicker.Reset(syncDuration) }` (keeping the
  period just set), or `delayTicker.Reset(max(syncDuration, time.Millisecond))`.
- **Found**: 2026-10-12, by the proof of `syncWatchersLoop` (the watchable store, unit 3b).
