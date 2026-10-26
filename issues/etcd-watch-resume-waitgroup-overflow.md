---
upstream: none
checked: 2026-10-26
links: []
---

# A reconnect with 2^31 or more watches on one stream panics in `waitCancelSubstreams`

- **Status**: bug (a reachable panic in the language's semantics; out of reach in practice: it
  needs 2^31 watches on one gRPC watch stream, each with its own goroutine). Present at upstream
  `main` and at the pinned `upamanyus/etcd` `16f73d6eb`. Fixed on the fork branch
  `watch-resume-fixes` (`b3c29bc17`, on `16f73d6eb`; not pushed, not yet the pin). It has no
  regression test: the test would need 2^31 watches.
- **Where**: `client/v3/watch.go` at `upamanyus/etcd` `16f73d6eb`: `waitCancelSubstreams` (988–1025;
  990: `wg.Add(len(w.resuming))`), called by `newWatchClient` (963) on each reconnect with every
  substream in `w.resuming`.
- **What happens**: `sync.WaitGroup`'s counter is an `int32` (`Add`: `v := int32(state >> 32)`;
  `if v < 0 { panic("sync: negative WaitGroup counter") }`, Go 1.27). With `len(w.resuming) = n`:
  - `2^31 ≤ n < 2^32`: the counter is negative, and `Add` panics;
  - `n = 2^32 + m`: the counter is `m`, so `Wait` may return while goroutines still run, and the
    `(m+1)`th `Done` panics.

  Every watch on the stream is in `w.resuming` at a reconnect, and a reconnect follows any
  transient stream error (`Unavailable`, `Internal`). Before the reconnect each watch has a live
  `serveSubstream` goroutine, so reaching it takes 2^31 goroutines (terabytes of stacks).
  The panic itself is easy to show: `var wg sync.WaitGroup; wg.Add(1 << 31)` panics.
- **Expected**: a reconnect does not depend on the number of watches fitting in an `int32`.
- **How the proof handles it**: the reconnection's proof (D25, `notes/decisions.md`) has to show
  `Add`'s precondition, a counter below `2^31` (Perennial's `sync.WaitGroup.Add` spec). The model's
  only bound on live goroutines is the thread bound (`threadBound GF ≤ 2^31`, a premise of
  `isClientWatcher`), and it does not bound `len(w.resuming)` at that point. By then the resumed
  goroutines may have called `Done` and exited, and nothing ties the number of watches to the
  threads still running. Per-goroutine `Add(1)` calls are bounded by the thread tokens of the
  goroutines already started (as for the stream's own wait group, `InvWatchWg.lean`). So the proof
  is over the fixed code.
- **Possible fixes**: call `wg.Add(1)` before each `go` in the loop (the fork's fix); or loop
  `Add` over chunks below `2^31`.
- **Found**: 2026-10-20, writing `waitCancelSubstreams`'s general spec (D25, stage S1d).
