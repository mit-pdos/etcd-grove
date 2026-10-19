# mutex-lock-recreated

## Security

Not a security report. Mutual exclusion through `concurrency.Mutex` holds only among cooperating clients: any client
with write access to the lock prefix can already break it by deleting keys. The bug needs two `Mutex` values on the
same session (one client's own lease) and breaks only that client's exclusion against other sessions; no member
crashes or hangs, no acknowledged data is lost, no auth check is skipped. Lock bugs have been public issues upstream
before (#22082, #19597).

## Candidate

- **Finding**: `issues/mutex-lock-recreated.md`
- **Target**: etcd-io/etcd, `main`
- **Branch**: `fix/mutex-lock-recreated` in `~/etcd-fixes/mutex-lock-recreated`, two commits, rebuilt 2026-10-18:
  b28d26713 adds the test, which fails there; 34adb1693 is the fix. Force-pushed 2026-10-19 to `upamanyus/etcd` (replacing e8c9187e5); the issue's test link (`#L64-L115`) checked on GitHub: the test, doc comment to closing brace. The fork's older draft branch
  `mutex-lock-recreated` (113b0b324, the keep-waiting fix) is left as it was.
- **Base**: upstream `main` 22cc5d9acd4a5953dfdfc2594dbeb53da89bb0d4 (2026-10-18); `client/v3/concurrency/mutex.go`
  and the test's package unchanged since b25719d10 and f061acd09, where the finding was made
- **State**: draft (revised to the skill's 2026-10-18 standard)
- **Upstream issue**: —
- **PR**: —

Commit messages (drafts for the user to rewrite):

- `client/v3: test Mutex.Lock when its key is recreated while waiting` (no body)
- `client/v3: fail Mutex.Lock when its key was recreated while waiting`, body: "Lock could succeed while another
  session held the lock, if another Mutex on the same session deleted and recreated their shared key during the
  wait."

## Duplicates checked (2026-10-16, rechecked 2026-10-18)

The finding was searched on 2026-10-16 before this candidate. Searches then (3): open PRs `mutex lock`, `mutex same
session`, `TryLock`. No duplicate. Rechecked 2026-10-18: a search for `mutex lock` created since 2026-10-14 finds
nothing; #22082, #22115 and #22387 are still open, unmerged. Related:

- #22082 (issue, open) / #22115 (PR, open): a stale `Unlock` retry deletes a newer same-session key; #22115 fences
  `Unlock` with `IsOwner()` (its diff, read 2026-10-18, touches only `Unlock`). Does not touch `Lock`'s final
  check; this bug remains with it (the deletion here is `TryLock`'s own delete, or `Unlock` of the `Mutex` that
  created the key, which the fence allows). Merges cleanly with this branch (`git merge-tree`, 2026-10-18).
- #22387 (PR, open, fixes #19597): `waitDeletes` also watches the waiter's own key and `Lock` returns
  `ErrSessionExpired` as soon as it is deleted. It does not fix this bug: the key can be deleted and recreated
  while no watch is open (between `tryAcquire` and `waitDeletes`' first `Get`, or between `waitDeletes` returning
  and `Lock`'s final `Get`). Measured 2026-10-18: this branch's test on the tests commit merged with #22387's head
  (no fix) fails 15 times in 20 (`m2.Lock` returns nil). Merges cleanly with this branch. The two changes are
  compatible: both return `ErrSessionExpired` when the key `Lock` waited on is gone.
- #19598 (PR, closed): earlier attempt at #19597. #16396, #11429, #11364: about mutexes and sessions, not this bug.

## Verification (go1.27.2 linux/amd64)

`TestMutexLockKeyRecreated` (`tests/integration/clientv3/concurrency/mutex_test.go`, after
`TestMutexLockSessionExpired`, on the package's lazy single-member cluster) is the issue's example: sessions `s1`,
`s2`, `s3`; `m1` locks; a watch on the prefix from the revision after `m1`'s lock orders the steps (one event per
step: `m2`'s put, `m2b.TryLock`'s delete, `m3`'s put, `m2b`'s put); `m1` unlocks, `m3.Lock` returns nil; then, if
`m2.Lock` returns within a second, it must return an error. It asserts only the guarantee (`m2` does not lock while
`m3` holds the lock), not which error, so it also passes with the keep-waiting design (the select's timeout case).

- At the tests commit b28d26713 (`cd tests && go test ./integration/clientv3/concurrency/ -run
  'TestMutexLockKeyRecreated$' -count=3`): fails every time, at line 110:

  ```
  --- FAIL: TestMutexLockKeyRecreated (0.10s)
          	Error:      	An error is expected but got nil.
          	Messages:   	m2 locked while m3 holds the lock
  ```

- At the fix commit 34adb1693, all pass:
  - `go test ./integration/clientv3/concurrency/ -run 'TestMutexLockKeyRecreated$' -count=5` (0.7 s for five: `m2.Lock`
    fails at once, not through the timeout), and `-race -count=20`
  - `go test -race ./integration/clientv3/concurrency/ -count=1` (the package)
  - `cd client/v3 && go test ./concurrency/ -count=1`
  - `go test ./integration/clientv3/experimental/recipes/ -run Mutex -count=1` and `go test ./integration/ -run
    TestV3Lock -count=1` (`TestV3LockLockWaiter`; callers of `Mutex`: recipes, the v3lock service)
  - `go vet` of both packages; `gofmt -l client/v3/concurrency tests/integration/clientv3/concurrency`: empty

Other runs (scratch tests, not committed; at b25719d10, where `mutex.go` was the same):

- With the fix, `m2.Lock` returns `mutex: session is expired`, then `m3.Unlock` and `m2b.Lock` return nil. At the
  base, `IsOwner()` is false for `m2` and true for `m3` after both `Lock`s return (the issue's "Anything else").
- Without `m2b.Lock` (the key stays deleted), `m2.Lock` returns `mutex: session is expired` at the base (the
  issue's parenthesis).
- The canceled-`Lock` variant (the finding's schedule: `A.Lock` canceled while `B.Lock` on the same session waits,
  then `D.Lock` on another session, then `A.Lock` again): the old draft test `TestMutexLockSharedSessionKeyRecreated`
  (113b0b324) fails at the base with `B.Lock` returning nil; with this fix `B.Lock` returns `mutex: session is
  expired` (that old test expects B to keep waiting, so it still fails there, by design of the other fix).

Not run: the v3lock service variant (a client canceling a waiting `Lock` RPC and retrying with the same lease while
another `Lock` RPC on that lease waits), `tests/e2e`, `make verify`, `golangci-lint`.

## Why the fix works

At the base, `m2.Lock` puts `s2`'s key (revision r1) and waits for keys created before r1 (`m1`'s).
`m2b.TryLock` sees the key exists, takes r1, finds `m1` the owner and deletes the key. `m3.Lock` puts `s3`'s key
(r2). `m2b.Lock` puts `s2`'s key again (r3 > r2) and waits for `m3`. When `m1` unlocks, `m2`'s wait (keys before
r1) is over, its `Get` finds `s2`'s key (now at r3) and `Lock` returns nil, although `m3`'s key (r2) is the oldest.
With the fix, the `Get` compares the key's create revision with r1: r3 differs, so `m2.Lock` returns
`ErrSessionExpired`. A create revision changes only when the key is deleted and created again, so the check
rejects nothing else: two `Mutex` values that share an unbroken key (`TestMutexSessionRelock`) still both lock.

The test is not a misuse: two `Mutex` values on one session and prefix are supported (`TestMutexSessionRelock` in
`tests/integration/clientv3/experimental/recipes/v3_lock_test.go`), and `TryLock` is documented to clean up when the
lock is held by another session, which is what deletes the shared key.

## If a reviewer asks

- Why an error and not keep waiting (the finding's first proposal, 113b0b324: loop on `waitDeletes`, then `Get`,
  adopting the new create revision): the loop treats the recreated key as the session's place in the queue, as
  `tryAcquire` does for an existing key, and `m2.Lock` would return nil after `m3` unlocks; but it is a larger
  change (the body of `Lock` in a loop), and the error is what `Lock` already returns when the key is gone, and
  what #22387 returns when the key is deleted during the wait. The issue asks the maintainers which they prefer;
  the test passes with either.
- `ErrSessionExpired` with a live session: `Lock` already returns it whenever the key is gone after the wait (a
  `TryLock` or `Unlock` on the same session deleted it), and its comment says "is the session key lost?" (now "lost
  or recreated?"). A new error would be more precise, at the cost of a new exported error.
- `Lock` does not delete the key on this path: the recreated key belongs to the other `Lock` (`m2b`), as on the
  existing `ErrSessionExpired` path. `m2`'s `myKey`/`myRev` stay set there, as on the existing path, so an `Unlock`
  of `m2` after the failed `Lock` would delete `m2b`'s key; callers do not unlock after a failed `Lock` (etcdctl,
  the v3lock service and `NewLocker` return or panic), and #22115's `IsOwner` fence on `Unlock` would refuse it.
- Why the test waits at most a second for `m2.Lock`: to assert only that `m2` does not lock while `m3` holds the
  lock, whichever design is chosen. At the base `m2.Lock` returns nil within milliseconds of `m1.Unlock`; the timeout
  can only make a broken build pass if `m2.Lock` is slower than a second, never fail a correct one.
- The v3lock service (`server/etcdserver/api/v3lock/lock.go`) creates a session with the request's lease and a
  new `Mutex` per `Lock` RPC, so two `Lock` RPCs with one lease are two `Mutex` values on one session; the
  canceled-`Lock` variant applies (code reading; not run).
- `Election.Campaign` has a related gap (it checks nothing after its wait): a separate finding,
  `issues/election-campaign-key-check.md`, not part of this change.
- Backports: `release-3.6` and `release-3.5` have the same final check (`len(gresp.Kvs) == 0` only) and the same
  `tryAcquire`; not run there.
