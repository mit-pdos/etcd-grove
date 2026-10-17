---
upstream: known
checked: 2026-10-16
links:
  - etcd-io/etcd#22296 issue open: same bug (time.Since zero on Windows' coarse monotonic clock, Ticker.Reset panics); no maintainer response
  - etcd-io/etcd#22297 pr open: same bug, fix
---

# server/storage/mvcc: `syncWatchersLoop` resets its ticker with a zero duration, a panic

- **Status**: open (not filed; no fix branch yet).
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
  Go documents), and `Spec/time/Since.lean` assumes `time.Since` returns a positive duration —
  an explicit, documented clock assumption (an axiom of this repository, in the mvcc collection);
  under it `watchableStore.syncWatchersLoop` (`Proof/go_etcd_io/etcd/server/v3/storage/mvcc/
  watchableStore__syncWatchersLoop.lean`) is panic-free. Without it the call is not provable, which
  is how the finding surfaced.
- **Possible fixes**: `if syncDuration > 0 { delayTicker.Reset(syncDuration) }` (keeping the
  period just set), or `delayTicker.Reset(max(syncDuration, time.Millisecond))`.
- **Found**: 2026-10-12, by the proof of `syncWatchersLoop` (the watchable store, unit 3b).
- **Fix verified** (2026-10-17, branch `pr-verify/etcd-22297`, report
  `notes/pr-verify/etcd-22297.md`): etcd-io/etcd#22297 (head `8a7b19d0c`) moves the delay into
  `resyncDelay`, which falls back to `watchResyncPeriod` unless `syncDuration > 0`. Over the PR,
  `syncWatchersLoop`'s unchanged spec is proved with Perennial's `time.wp_Since` (any duration):
  the clock assumption `Spec/time/Since.lean` (axiom `time.Since.wp_proof`) is deleted there.
