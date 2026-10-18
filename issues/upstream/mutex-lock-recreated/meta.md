# mutex-lock-recreated

- **Finding**: `issues/mutex-lock-recreated.md`
- **Target**: etcd-io/etcd, `main`
- **Branch**: `fix/mutex-lock-recreated` in `~/etcd-fixes/mutex-lock-recreated` (commit e8c9187e5), pushed 2026-10-18 to `upamanyus/etcd`
  (`https://github.com/upamanyus/etcd/tree/fix/mutex-lock-recreated`), the branch the links in `issue.md` name. The fork's older
  draft branch `mutex-lock-recreated` (113b0b324) is left as it was.
- **Base**: upstream `main` b25719d10cdc41fb707b0d9f819c2529dec5d590 (2026-10-16); `client/v3/concurrency/mutex.go`
  unchanged since f061acd09, where the finding was made
- **State**: draft
- **Upstream issue**: —
- **PR**: —

## Duplicates checked (2026-10-16)

The finding was searched on 2026-10-16 before this candidate. Searches here (3): open PRs `mutex lock`, `mutex same
session`, `TryLock`. No duplicate. Related:

- #22082 (issue, open) / #22115 (PR, open): a stale `Unlock` retry deletes a newer same-session key; #22115 fences
  `Unlock` with `IsOwner()`. Does not touch `Lock`'s final check; this bug remains with it (the deletion here is
  `TryLock`'s own delete, or `Unlock` of the `Mutex` that created the key, which the fence allows).
- #22387 (PR, open, fixes #19597): `waitDeletes` also watches the waiter's own key and `Lock` returns
  `ErrSessionExpired` as soon as it is deleted. With it, the issue's example no longer fails (`m2.Lock` returns
  `ErrSessionExpired` at `m2b.TryLock`'s delete), but the key can still be deleted and recreated while no watch is
  open: between `tryAcquire` and `waitDeletes`' first `Get`, or between `waitDeletes` returning and `Lock`'s final
  `Get`. So #22387 does not fix this bug; it narrows it to those windows (by reading the PR's diff; not run).
  The two changes are compatible: both return `ErrSessionExpired` when the key Lock waited for is gone.
- #19598 (PR, closed): earlier attempt at #19597. #16396, #11429, #11364: about mutexes and sessions, not this bug.

## Verification

`TestMutexLockKeyRecreated` (`tests/integration/clientv3/concurrency/mutex_test.go`) is the issue's example. At the
base (fix reverted): `cd tests && go test ./integration/clientv3/concurrency/ -run TestMutexLockKeyRecreated
-count=1` fails at line 125, "Expected error with "mutex: session is expired" in chain but got nil" (`m2.Lock`
returned nil).

With the fix, all pass:

- `cd tests && go test ./integration/clientv3/concurrency/ -run TestMutexLockKeyRecreated -count=5`, and
  `-race -count=20`
- `cd tests && go test -race ./integration/clientv3/concurrency/ -count=1` (the package)
- `cd client/v3 && go test ./concurrency/ -count=1`
- `cd tests && go test ./integration/clientv3/experimental/recipes/ -run Mutex -count=1` and
  `go test ./integration/ -run TestV3Lock -count=1` (callers of `Mutex`: recipes, the v3lock service)
- `go vet` of both packages, `gofmt -l client/v3/concurrency tests/integration/clientv3/concurrency`: clean

Other runs at the base (scratch tests, not committed):

- The issue's output: each call's result logged, at the base; with the fix the same run gives `m2.Lock: mutex:
  session is expired`, then `m3.Unlock: <nil>`, `m2b.Lock: <nil>`. At the base, `IsOwner()` is false for `m2` and
  true for `m3` after both `Lock`s return.
- Without `m2b.Lock` (the key stays deleted), `m2.Lock` returns `mutex: session is expired` at the base (the
  issue's expectation).
- The canceled-`Lock` variant (the finding's schedule: `A.Lock` canceled while `B.Lock` on the same session waits,
  then `D.Lock` on another session, then `A.Lock` again): the old draft test
  `TestMutexLockSharedSessionKeyRecreated` (113b0b324) fails at the base with `B.Lock` returning nil; with this fix
  `B.Lock` returns `mutex: session is expired` (that old test expects B to keep waiting, so it still fails there,
  by design of the other fix).

Not run: the v3lock service variant (a client cancelling a waiting `Lock` RPC and retrying with the same lease
while another `Lock` RPC on that lease waits), `tests/e2e`, `make verify`, `golangci-lint`.

## If a reviewer asks

- Why an error and not keep waiting (the finding's first proposal, 113b0b324: loop on `waitDeletes`, then `Get`,
  adopting the new create revision): the loop treats the recreated key as the session's place in the queue, as
  `tryAcquire` does for an existing key, and `m2.Lock` would return nil after `m3` unlocks; but it is a larger
  change (the body of `Lock` in a loop), and the error is what `Lock` already returns when the key is gone, and
  what #22387 returns when the key is deleted during the wait. The issue asks the maintainers which they prefer.
- `ErrSessionExpired` with a live session: `Lock` already returns it whenever the key is gone after the wait (a
  `TryLock` or `Unlock` on the same session deleted it), and its comment says "is the session key lost?". A new
  error would be more precise, at the cost of a new exported error.
- `Lock` does not delete the key on this path: the recreated key belongs to the other `Lock` (`m2b`), as on the
  existing `ErrSessionExpired` path.
- The v3lock service (`server/etcdserver/api/v3lock/lock.go`) creates a session with the request's lease and a
  new `Mutex` per `Lock` RPC, so two `Lock` RPCs with one lease are two `Mutex` values on one session; the
  canceled-`Lock` variant applies (code reading; not run).
- Backports: `release-3.6` and `release-3.5` have the same final check (`len(gresp.Kvs) == 0` only) and the same
  `tryAcquire`; not run there.
