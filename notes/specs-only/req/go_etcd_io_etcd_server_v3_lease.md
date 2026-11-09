# Requirements on `go.etcd.io/etcd/server/v3/lease` (3c)


## from 2c

What the request path (2c) needs of the lessor (3c) and `lease/leasehttp`:

1. **`Lookup(id)`, `Leases()`**: leases of the member's applied state (each id in W0's `granted`),
   their keys attached at the member's applied revision, `Remaining()`/`TTL()` any; `Demoted()`.
2. **`Renew(id)`**: a TTL, `ErrLeaseNotFound` or `ErrNotPrimary` (any time: W0's keep-alive step
   says nothing of liveness).
3. **`leasehttp.RenewHTTP`, `TimeToLiveHTTP`** (the forwarding to the leader): the leader's answer,
   one W0's step allows at every later state, `ErrLeaseNotFound`, or other errors (retried).

## from 2d

1. **`ExpiredLeasesC()`** (`run`'s expiry arm): a receive gives a `[]*Lease` (`expiredLeases sl ids`,
   provisional in `ApiApply.lean`), and only when the environment lets leases expire
   (`γ.cfg.leaseExpiry = true`; with `false`, the deployment premise that no lease expires during the
   run, the channel never delivers). Used by: `run.spec`, `revokeExpiredLeases.spec`.
2. **`Promote(d)`, `Demote()`** (`applyEntryNormal`'s empty entry at a leader, the ready handler's
   `updateLeadership`): no effect on the model; no panic.
3. **`Recover(newbe, rd)`** (`applySnapshot`): over a snapshot's image, before mvcc's `Restore`.

## from 2e

1. `EtcdServer.leaseBootRes cfg ecfg` (provisional slot of `NewServer`): the lessor's configuration
   against W0's `EnvCfg.leaseExpiry`. **With `leaseExpiry = false`** the server cannot fire a lease
   expiry, so the lessor's slot must carry the deployment premise that no lease expires during the
   run (time-based: 3c to state it, or the user decides to drop the mode: open question Q6 of
   `batch-2e.md`).
2. `lessor.Stop` once (`Cleanup`, through `srvClosers`).
