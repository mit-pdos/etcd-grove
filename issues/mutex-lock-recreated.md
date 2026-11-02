---
upstream: reported
checked: 2026-11-01
links:
  - etcd-io/etcd#22613 issue open: this bug, reported 2026-10-19
  - etcd-io/etcd#22617 pr open: the fix, opened 2026-10-19
  - etcd-io/etcd#22082 issue open: related, not this bug (same-session key recreated with a newer create revision; Unlock deletes it unfenced, here Lock returns without checking myRev)
  - etcd-io/etcd#22115 pr open: related, not this bug (fences Unlock with IsOwner; Lock's final existence-only check unchanged)
  - etcd-io/etcd#22387 pr open: related (fixes #19597): Lock returns ErrSessionExpired when its key is deleted during the wait, which narrows this bug but does not fix it (deletion and recreation between Lock's RPCs): the test still fails in 15 of 20 runs with it (2026-10-18)
blocks-proof: yes
---

# concurrency: Mutex.Lock returns while another session holds the lock

`Mutex.Lock` (`client/v3/concurrency`) can return nil while another session holds the lock, when
another `Mutex` on the same session and prefix deletes the session's key during the wait (a failed
`TryLock` or a canceled `Lock`) and a `Lock` on that session recreates it after another session's
key: two callers then both believe they hold the lock (`IsOwner()` fencing still fails correctly).
The v3lock service reaches it when a client retries a canceled `Lock` RPC with the same lease while
another `Lock` RPC on that lease waits.

**Reproduction:** `TestMutexLockKeyRecreated` in
[`issues/mutex-lock-recreated/mutex_recreated_test.go`](mutex-lock-recreated/mutex_recreated_test.go),
copied into `tests/integration/clientv3/concurrency` at
etcd-io/etcd@1573d59416efa220421c451f5266b24a5d8374ef (2026-10-28), go1.27.3:

```
$ go test ./integration/clientv3/concurrency -run '^TestMutexLockKeyRecreated$' -count=1
--- FAIL: TestMutexLockKeyRecreated (0.25s)
        	Error:      	An error is expected but got nil.
        	Messages:   	m2 locked while m3 holds the lock
FAIL
```

## Proof

yes: it makes the property a top-level adequacy test over this code checks false for a workload such a test may use, and no fix is in the goosed fork yet; the proof sidesteps it: the proved spec of `Lock` has a weaker outcome, `keyRecreated` (the key present with a later
create revision, not `lockedAt`), so mutual exclusion holds only for one `Mutex` per session and
prefix (`Proof/go_etcd_io/etcd/client/v3/concurrency/InvMutex.lean`); the verified fork carries no
fix.

## Fix

**Branch**: `fix/mutex-lock-recreated` in `~/etcd-fixes/mutex-lock-recreated` (upamanyus/etcd, pushed): b28d26713 test, 34adb1693 fix
**Base**: etcd-io/etcd@22cc5d9acd4a5953dfdfc2594dbeb53da89bb0d4

## Notes

The PR returns `ErrSessionExpired` when the key's create revision differs from `m.myRev`; the
issue asks whether the maintainers prefer `Lock` to keep waiting (the older draft branch
`mutex-lock-recreated`, 113b0b324). The test asserts only that `m2` does not lock while `m3` holds
the lock, so it passes with either.
