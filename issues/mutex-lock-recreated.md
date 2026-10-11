# concurrency: Mutex.Lock can return nil while another session holds the lock

## Summary

`Mutex.Lock` in `client/v3/concurrency` can return nil while a key of another session is the first-created key under the lock prefix, so two callers both believe they hold the lock. This needs two `Mutex` values on the same session and prefix, one of which is canceled while waiting and then locks again. The affected caller's `IsOwner()` comparison is false, so transactions guarded by it fail, but code that relies on `Lock` returning nil is not mutually excluded. The v3lock service can reach this state from a client that retries a canceled `Lock` RPC with the same lease. I found this while formally verifying the concurrency package.

## What happens

Line references are to `client/v3/concurrency/mutex.go` at f061acd09.

Two `Mutex` values on one session share the key `pfx/<lease>`. `tryAcquire` (lines 111-132) creates that key if it is absent; otherwise it takes the `Else` branch and reuses the existing key, recording its create revision in `m.myRev` (lines 127-130). A waiting `Lock` then waits for every key under the prefix created before `m.myRev` (`waitDeletes(ctx, client, m.pfx, m.myRev-1)`, line 89), checks only that `m.myKey` still exists (`Get`, lines 97-105), and returns nil (lines 106-108). It does not check that the key's create revision is still `m.myRev`.

Schedule, with mutexes A and B on session S, C on session T, D on session U, all on the same prefix:

1. C locks.
2. A calls `Lock`; it creates `pfx/<lease S>` at revision r1 and waits behind C.
3. B calls `Lock`; it reuses the same key, with `myRev = r1`, and waits behind C.
4. A's context is canceled. Its `Lock` calls `Unlock` (lines 91-93), which deletes the shared key (line 144).
5. D calls `Lock`; it creates its key at r2 > r1 and waits behind C.
6. A calls `Lock` again; it recreates `pfx/<lease S>` at r3 > r2 and waits behind C and D.
7. C unlocks.

D's key is now the first-created key, and D's `Lock` returns nil. B's `waitDeletes(r1-1)` has nothing left to wait for, its `Get` finds `pfx/<lease S>` (now at r3), and B's `Lock` also returns nil. B's `IsOwner()` (`CreateRevision(myKey) == myRev`, line 153) compares against r1 and is false.

## How to reproduce

`TestMutexLockSharedSessionKeyRecreated` in `tests/integration/clientv3/concurrency/mutex_recreated_test.go` (on the branch below) runs this schedule; without the fix it fails with B's `Lock` returning nil while D holds the lock; `TestMutexLockSeparateSessionsKeyNotRecreated` runs the same schedule with B on its own session and passes. The v3lock service (`server/etcdserver/api/v3lock/lock.go`, lines 35-49) creates a new session with the request's lease and a new `Mutex` for every `Lock` RPC, so a client that cancels a waiting `Lock` RPC and retries it with the same lease, while another `Lock` RPC on that lease is still waiting, triggers the same schedule.

## Expected

`Lock` returns nil only when the caller's key, with the create revision it waited for, is the first-created key under the prefix. In the schedule above, B should keep waiting until D unlocks.

## Proposed fix

Branch `mutex-lock-recreated`: after the final `Get`, if the key's create revision differs from `m.myRev`, set `m.myRev` to the new revision and wait again for the keys created before it, looping until the key found is the one waited for. This is how `tryAcquire` already treats an existing key of the same session, as that session's place in the queue. I considered returning an error instead (a new error, or `ErrSessionExpired`), but that would make `Lock` fail for a caller whose context was not canceled and whose session is alive, only because another `Mutex` on the same session was canceled, and would leave retrying to every caller. `TryLock` does not wait and is unchanged.
