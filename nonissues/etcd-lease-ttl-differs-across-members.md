---
upstream: none
checked: 2026-11-05
links: []
blocks-proof: no
---

# lease: `TimeToLive` reports different TTLs for one lease when the members' election timeouts differ

Each member raises a granted lease's TTL to its own minimum, which is 1.5 election timeouts
(`--election-timeout`). In a cluster whose members are configured with different election
timeouts, `TimeToLive` for one lease can therefore report a different `GrantedTTL` depending on
the member that answers. On one member, the value can also change when the member restores a
snapshot: `initAndRecover` rebuilds every lease from the snapshot's records, which carry the
sending member's TTL, and raises each to its own minimum. For example, a member at minimum 2 applies
`Grant(5)` and records TTL 5; after it restores a snapshot from a member at minimum 10, the same
lease has TTL 10.

**Why not an issue:** no test; found by code reading
([`server.go:344`](https://github.com/upamanyus/etcd/blob/249d76bea78d0c8980251d5fa7b26c35ef21263a/server/etcdserver/server.go#L344),
[`lessor.go:301`](https://github.com/upamanyus/etcd/blob/249d76bea78d0c8980251d5fa7b26c35ef21263a/server/lease/lessor.go#L301),
[`lessor.go:817`](https://github.com/upamanyus/etcd/blob/249d76bea78d0c8980251d5fa7b26c35ef21263a/server/lease/lessor.go#L817)).
etcd documents no guarantee that `GrantedTTL` is the same on every member, and members are
normally configured with the same election timeout.

## Proof

no: the lease-expiry proof's law that an id's TTL agrees across the lessor's history
(`lease.leaseTTLAt_ttl_agree`) is false once snapshots carry leases. The S2–S4 plan
(`notes/lease-expiry-plan.md`) replaces it with "every recorded TTL ≥ the member's minimum TTL"
(option (A), pending the user), which the top-level result needs without a premise.
