---
upstream: none
checked: 2026-11-09
links: []
blocks-proof: no
---

# recipes: DoubleBarrier.Leave, RWMutex.Unlock and RUnlock panic when no key of the process was created

`(*DoubleBarrier).Leave` (`client/v3/experimental/recipes/double_barrier.go`) panics with a nil
pointer dereference when other processes are waiting on the barrier and this `DoubleBarrier` has no
key of its own: a `Leave` without an `Enter`, or after an `Enter` that returned
`ErrTooManyClients` from its first check (before creating the key). `Leave` compares the waiters'
keys with `b.myKey.Key()`, and `myKey` is `nil` until `Enter` creates the key.

**Why not an issue:** an unstated precondition ("call `Leave` only after an `Enter` that created
this process's key") that every caller meets: etcd's integration tests call `Leave` only after a
successful `Enter`; nothing else in etcd uses the package. Found by code reading, no test.

## Proof

no: `DoubleBarrier.Leave.spec` takes `myKey` set (`dbOwn ... (some st)`), which a successful
`Enter.spec` gives (`SpecPlan/Spec/go_etcd_io/etcd/client/v3/experimental/recipes/DoubleBarrier__Leave.lean`,
batch 1f of the specs-only branch).

## Notes

- With no waiter left, `Leave` returns `nil` before reaching `myKey`, so the panic needs other
  processes' keys under `key/waiters`.
- A fix: `if b.myKey == nil { return nil }` (or an error) at `Leave`'s start; or document the
  precondition.
- Same precondition: `RWMutex.Unlock`/`RUnlock` (`rwmutex.go:88-89`) call `rwm.myKey.Delete()`, a
  promoted method through a nil `*EphemeralKV` when `Lock`/`RLock` was never called or failed before
  creating the key: a nil dereference. etcd's `testRWMutex` sends the handle to the unlocking
  goroutine even after a failed `Lock` (only after `t.Errorf`); the specs take `myKey` set.
- Same shape, also no caller affected: `WaitEvents` and `WaitPrefixEvents` (exported) index their
  `evs` argument on the first event, so an empty slice panics once an event arrives
  (`WaitEvents.spec`'s premise `ts ≠ []`).
