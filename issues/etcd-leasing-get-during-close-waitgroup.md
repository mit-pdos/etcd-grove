---
upstream: unchecked
checked: 2026-11-01
links: []
---

# The leasing KV's `Get` concurrent with its close function can panic in `sync.WaitGroup`

- **Status**: an unstated precondition (a reachable panic when it is broken): no `Get` may run
  concurrently with the close function `NewKV` returns, which neither documents. Found by reading,
  not reproduced. The same shape as `etcd-cache-watch-during-close-waitgroup`.
- **Where**: `client/v3/leasing/kv.go` at the fork's pin (`upamanyus/etcd` `633036387`): `get`
  (311-348; after a successful acquisition `lkv.wg.Add(1)` at 341 and the lease monitor's
  goroutine), `Close` (80-83: `lkv.cancel()` then `lkv.wg.Wait()`; the close function `NewKV`
  returns). Go 1.27's `sync/waitgroup.go` `Add` (117-133), `Wait` (200-215).
- **What happens**: the close function cancels the KV's context; the session monitor,
  `clearOldRevokes` and the lease monitors return and the counter can reach zero while `Wait`
  waits. A `Get` that acquired a lease then runs `Add(1)`: as for the cache, "Add called
  concurrently with Wait" or "WaitGroup is reused before previous Wait has returned", or, after
  `Wait` returned, a lease monitor that outlives the close.
- **Expected**: the close function documents that it must not overlap the KV's operations, or
  `get` checks a closed flag under a lock the close takes before `Wait`.
- **How the proof handles it**: the "open" token `leasingOpen` (`Proof/go_etcd_io/etcd/client/v3/
  leasing/InvLeasingKV.lean`): `Get` takes a fraction, the close function the whole.
- **Possible fixes**: as for the cache: a closed flag guarding `Add(1)`, or documentation.
- **Found**: 2026-11-01, bounds plan B3's wait-group inventory (`notes/bounds-waitgroups.md`).
