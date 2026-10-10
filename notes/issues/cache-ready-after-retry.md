# cache: Cache never becomes ready again after a watch retry that purges the demux

## Summary

When the cache's upstream watch fails and the cache retries from a fresh Get, the retried watch can leave the cache permanently not ready. If the Get's revision is not right after the last revision the demux observed (the usual case when etcd has moved on during the retry, and always when the failed watch had observed no events), `demux.Init` purges the demux on the retried watch's first response; the purge stops the store watcher that was just registered for that same watch, the watch loop goes around once, and `ready.Set()` is never called again because it sits behind a `sync.Once` that is already spent. The upstream watch keeps flowing and the store stays current, but `Ready()` stays false, `WaitReady` never returns, and `Cache.Watch` blocks until its context is canceled. We found this while formally verifying the cache package.

## What happens

References are to `main` at f061acd0902d489041448cdd19d71a345d27b9f5.

1. `getWatchLoop` calls `getWatch` (`cache/cache.go:331`), which does a Get, `store.Restore`s it (`cache.go:344`) and calls `watch(rev)` with `rev = Get revision + 1`.
2. `watch` (`cache.go:348`) creates `readyOnce` once per call (`cache.go:349`), then in its loop creates the store watcher `storeW` and registers it with the demux (`cache.go:351-352`), starts `applyStorage(storeW)` (`cache.go:355-361`), and calls `watchEvents`.
3. `watchEvents` (`cache.go:388`) opens the upstream watch at `rev`, and on its first response runs
   `readyOnce.Do(func() { c.demux.Init(rev); c.ready.Set() })` (`cache.go:405-408`).
   So `Init` runs after `storeW` is registered.
4. `demux.Init` (`cache/demux.go:119`) purges the demux when the demux was initialized before and either never saw an event (`maxRev == 0`, `demux.go:130-134`) or `rev != maxRev+1` (`demux.go:141`). `purge` (`demux.go:296`) stops every registered watcher (`demux.go:301,304`), including the `storeW` registered in step 2.
5. `applyStorage` sees `storeW`'s channel closed and returns nil (`cache.go:378-379`); the goroutine closes `applyErr`. `watchEvents` receives nil from it, calls `c.ready.Reset()` and returns nil (`cache.go:418-420`). Note that `ready.Set()` ran in step 3 just before this, so the cache is briefly ready.
6. `watch` unregisters `storeW` and, the error being nil, loops (`cache.go:363-368`): a new `storeW` is registered at the same `rev` and a new upstream watch is opened. This time nothing is purged (the demux now has `minRev == rev`, and `Init` is not called again anyway), so events flow: `Broadcast` succeeds and the new `storeW` applies them to the store. But `readyOnce` is spent, so `ready.Set()` never runs again for this `watch` call, and `watch` only returns on an error. `Ready()` stays false for as long as the upstream watch stays healthy.

The first watch after `New` does not hit this, because the demux is fresh (`minRev == 0`, `demux.go:125-128`) and `Init` does not purge. A retry whose Get returns exactly the last revision the demux saw (`rev == maxRev+1`, `demux.go:136-138`) does not hit it either.

## How to reproduce

The branch below adds `TestCacheReadyAfterWatchRetry` (`cache/watch_retry_test.go`). It uses a fake `clientv3.Watcher` that gives each `Watch` call its own response channel, so the test decides which upstream watch each response goes to. The scenario: the first Get answers revision 9, the cache watches from 10, the watch is created and the cache becomes ready; optionally an event at revision 10 is delivered; then the upstream watch is canceled with an error and the cache becomes not ready. The retry's Get answers revision `R`, the cache watches from `R+1`, the retried watch is created, an event at `R+1` is delivered on it, and the test checks that the store reaches `R+1`, that the cache becomes ready, and that a `Cache.Watch` from `R+1` receives the event.

- With `R = 10` and the event at 10 (the retry continues the demux), the test passes on `main`.
- With `R = 12` and the event at 10 (`demux.go:141` purges), and with `R = 12` and no event (`demux.go:132` purges), the store reaches revision 13 but `WaitReady` times out on `main`.

```
go test ./cache/ -run TestCacheReadyAfterWatchRetry -v
```

In a real deployment this is a cache whose upstream watch fails (for example, a canceled watch or a `Broadcast` validation error) while writes continue on etcd.

## Expected

After a retried upstream watch is established, the cache becomes ready again, as it does after the first watch, and `WaitReady` and `Cache.Watch` proceed.

## Proposed fix

Branch `cache-ready-after-retry` (one commit, with the test). `rev` is known when `watch` is entered, so `Init` does not need the first response. `watch` now calls `c.demux.Init(rev)` once, before the loop and so before the first `storeW` is registered; a purge then only stops watchers of earlier watches. The first response of the upstream watch still gates readiness, now just `readyOnce.Do(c.ready.Set)`.

Alternatives that do not work:

- A new `sync.Once` per loop iteration (so `Init` and `ready.Set` run again on each iteration's first response): after the purge `maxRev` is 0, so every iteration's `Init` takes the `maxRev == 0` branch, purges again and stops that iteration's `storeW`, and `watch` reopens the upstream watch in a loop. The test above catches this (it fails after ten reopened watches).
- Dropping the `Once` and calling `ready.Set()` on every first response, with `Init` still in `watchEvents`: same purge loop, with readiness flapping.

With `Init` out of the loop, one `Once` per `watch` call is enough: nothing else purges the demux (`demux.Purge` and `demux.Compact` are not called outside tests), and a `storeW` is otherwise stopped only when it lags behind the demux history, in which case the next iteration's upstream watch, restarted from the same `rev`, replays revisions the demux rejects as stale, so the cache retries from a new Get with a new `watch` call.

## Also noticed

Two observations from the same verification, for the maintainers' judgment; neither is a bug and the branch does not change them:

- Each upstream watch is opened with `c.internalCtx` (`cache.go:390`) and is never canceled when `watchEvents` returns, so every retry leaves the previous upstream watch (client goroutines and server-side watcher) open until the cache is closed; in the scenario above, each round of the loop adds one. A child context canceled when `watchEvents` returns would close it.
- When `getWatch` returns and is retried, the previous iteration's `applyStorage` goroutine may still be draining the responses buffered in its stopped watcher while the next `Restore` or `Apply` runs. This is safe: every such response was broadcast before the retry's `Get`, so its revision is at most the `Get`'s, and `store.Apply` rejects it as stale through `validateRevisions` (`cache/store.go:126,178`); the goroutine's error goes to a channel nobody reads. We mention it because the safety argument is implicit in the code.
- `newCache` validates `HistoryWindowSize` and `BTreeDegree` but not `PerWatcherBufferSize`; a negative value makes `newWatcher`'s `make(chan …, bufSize)` panic. Should it be validated like the others?
