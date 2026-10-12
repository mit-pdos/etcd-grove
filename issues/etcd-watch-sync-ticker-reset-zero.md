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
