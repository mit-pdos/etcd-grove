---
upstream: unchecked
checked: 2026-10-17
links:
  - etcd-io/etcd#21600 pr open: related; its new store.waitForRev has the same lost wakeup (context.AfterFunc's Broadcast)
---

# cache: waitTillRevision can miss its cancellation and timeout wakeups

## Status

A bug (liveness): `Cache.Get` (linearizable) can ignore a canceled context and its `WaitTimeout`.
It waits until the store's revision changes next.

## Where

`cache/cache.go:268-304` at the pinned fork revision `09669450f` (`etc/goose.py`, project `etcd`).
The code is the same as upstream's: the fork's commits do not touch it.

```go
timeoutCh := time.After(c.cfg.WaitTimeout)
go func() {
	select {
	case <-timeoutCh:
		c.store.revCond.Broadcast()
	case <-ctx.Done():
		c.store.revCond.Broadcast()
	}
}()

c.store.mu.RLock()
defer c.store.mu.RUnlock()

for c.store.latest.rev < rev {
	if time.Since(startTime) >= c.cfg.WaitTimeout {
		return ErrCacheTimeout
	}
	if ctx.Err() != nil {
		return ctx.Err()
	}
	c.store.revCond.Wait()
}
```

## What happens

The goroutine's `Broadcast` does not take the store's lock. `sync.Cond` only wakes goroutines that
are already in `Wait`. So the waiter can lose the wakeup:

1. it checks the time and `ctx.Err()`, and both say "keep waiting";
2. the context is canceled, or the timer fires;
3. the goroutine broadcasts, but nobody is waiting yet;
4. the goroutine exits;
5. the waiter calls `Wait()`.

Nothing else is left to wake the waiter, for either event: the goroutine handled only one of them.
So `waitTillRevision`, and `Cache.Get` with it, returns only at the next `revCond.Broadcast`, i.e.
when the store's revision next changes (`Apply`, `Restore`, a progress notification).

- When the cache's upstream watch is healthy, the progress requestor (`add()`) makes that happen
  within about `ProgressRequestInterval` (100ms).
- When the watch is down, or in back-off, nothing advances the store. The `Get` then hangs past
  its context and past `WaitTimeout`, which is exactly the case the timeout is there for.

Reproduction: `notes/pr-verify/etcd-21600/waittillrevision_probe_test.go`, `TestWaitTillRevisionLostCancelWakeup`
(on branch `pr-verify/etcd-21600`).

- It is deterministic. The context's `Err()` is canceled while it is running: the call returns
  `nil`, then the context's `Done` closes and the canceler runs.
- It runs against the pinned fork `09669450f`:
  `cp waittillrevision_probe_test.go <fork>/cache/ && go test -run TestWaitTillRevisionLostCancelWakeup .`.
- `waitTillRevision` (with `WaitTimeout` 3s) is still blocked after 5s, and returns only when the
  test broadcasts `revCond` itself.

## Expected

- `waitTillRevision` returns the context's error soon after the context is canceled.
- It returns `ErrCacheTimeout` soon after `WaitTimeout`.

## How the proof handles it

It does not. The proof is of partial correctness: `Cache.waitTillRevision.spec`
(`Spec/go_etcd_io/etcd/cache/v3/Cache__waitTillRevision.lean`) only says what is returned if it
returns. Perennial's `Cond.Broadcast` spec does not need the lock.

## Possible fixes

Take the store's lock around the broadcasts (`c.store.mu.Lock(); c.store.revCond.Broadcast();
c.store.mu.Unlock()`). The waiter holds a read lock from its checks until `Wait` registers it, so
the broadcast can then only land before the checks or after the registration. This takes the
write lock, not a read lock: readers do not exclude each other. (`Wait` registers before it
releases its `RLocker`, so the write lock is free only once the waiter is registered.)

## Found

2026-10-17, while verifying etcd-io/etcd#21600 (its `store.waitForRev` copies the pattern, through
`context.AfterFunc`: `notes/pr-verify/etcd-21600.md`). Found by reading the code against
`sync.Cond`'s semantics. The proofs cannot see it.
