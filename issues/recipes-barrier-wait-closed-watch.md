# clientv3/experimental/recipes: Barrier.Wait returns nil (released) when its watch closes while the barrier is held

## Summary

`Barrier.Wait` (`client/v3/experimental/recipes`) blocks until the barrier key is deleted. If the watch it waits on closes first (the client is closed, or etcd cancels the watch because its start revision was compacted), `Wait` returns `nil`, which means "released", although the barrier key is still there. `DoubleBarrier.Enter` likewise returns `nil` before the barrier is full. I found this while formally verifying the recipes package.

## What happens

References are to `main` at f061acd0902d489041448cdd19d71a345d27b9f5.

1. `waitEvents` (`client/v3/experimental/recipes/watch.go:45-57`) returns `nil` when the watch channel closes before the awaited events, ignoring a canceled response's `Err()` (`ErrCompacted`). `WaitEvents` (`watch.go:25-33`) then returns `(nil, nil)`.
2. `Barrier.Wait` (`barrier.go:51-65`), when the key exists, returns the error of `WaitEvents(b.client, b.key, resp.Header.Revision+1, DELETE)`: `nil`. The caller proceeds as if the barrier had been released.
3. `DoubleBarrier.Enter` (`double_barrier.go:91-96`) returns the error of `WaitEvents(client, b.key+"/ready", ek.Revision(), PUT)`: `nil`, with fewer than `count` entrants. `Leave` (`double_barrier.go:146-170`) recurses into `Leave` after a `nil` from `WaitEvents`, which re-reads the waiters, so a closed watch there only costs a retry (or a `Get` error if the client is closed).
4. `RWMutex.waitOnLastRev` (`rwmutex.go:68-86`) returns `(false, nil)` after a closed watch, and `RLock`/`Lock` loop and re-read the blocking key: benign as well.

## How to reproduce

The branch below adds, in `tests/integration/clientv3/experimental/recipes/v3_closed_watch_test.go`:

- `TestBarrierWaitClientClosed`: client 0 holds `test-barrier`; a second client `Wait`s on it in a goroutine; after 500 ms (`Wait` has not returned), the test closes the second client, then checks with client 0 that the barrier key is still there.
- `TestDoubleBarrierEnterClientClosed`: one entrant on a `DoubleBarrier` of count 2, with a session on its own client; after 500 ms (`Enter` has not returned), the test closes that client.

On `main`:

```
TestBarrierWaitClientClosed: An error is expected but got nil. (Wait returned nil (released) while the barrier is held)
TestDoubleBarrierEnterClientClosed: An error is expected but got nil. (Enter returned nil with 1 of 2 entrants)
```

```
cd tests && go test ./integration/clientv3/experimental/recipes/ -run 'TestBarrierWaitClientClosed|TestDoubleBarrierEnterClientClosed' -v
```

No existing test encodes the old behaviour; the suite passes unchanged with the fix.

## Expected

`Wait` returns `nil` only once the barrier key has been deleted, and `Enter` only once `count` processes have entered; otherwise they return an error.

## The fix

Branch `recipes-closed-watch-channel`, the same commit as [recipes-dequeue-closed-watch](recipes-dequeue-closed-watch.md) (one cause): `waitEvents` returns the canceled watch's `Err()` (e.g. `ErrCompacted`), and a new `ErrWatchClosed` when the channel closes without the events; `WaitEvents` returns it, and `Wait` and `Enter` already return `WaitEvents`' error. After the fix both tests see `watch channel closed`. `RWMutex.Lock`/`RLock` and `DoubleBarrier.Leave` now also return that error instead of re-reading; with a closed client the re-read failed anyway, and on a compaction they fail instead of retrying.

The commit is one commit off `main` (f061acd09), as the other fix branches are.
