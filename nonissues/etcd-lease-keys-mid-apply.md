---
upstream: none
checked: 2026-11-09
links: []
blocks-proof: yes
---

# etcdserver: `LeaseTimeToLive` with `Keys` can return a key set that no revision had

On the leader, `LeaseTimeToLive(id, WithAttachedKeys())` reads the lease's key set while the apply
thread may be in the middle of applying an entry that changes it, so it can return part of the
change: during the revocation of a lease holding keys `a` and `b`, the answer can list `b` alone;
during a transaction that puts `a` and `b` with the lease at one revision, it can list `a` alone. No
revision of the store had that set of keys attached to the lease.

**Expected:** an answer from one point of the history: the keys attached at some revision.

**Why not an issue:** no test; found by code reading (batch 3c of the specs-only branch, the
lessor's specs). The key set is the `*Lease` object's `itemSet`, read under the object's own lock
alone (`Lease.Keys`, `server/lease/lease.go:106`). The apply thread changes it one key at a time:
`lessor.Revoke` deletes the keys through mvcc's write transaction, each delete calling
`Detach(id, [key])` (`server/lease/lessor.go:343-351`, `server/storage/mvcc/kvstore_txn.go:335`),
and a transaction's puts each call `Attach` (`kvstore_txn.go:285`); `leaseTimeToLive`
(`server/etcdserver/v3_server.go:637-664`) waits for the applied index, then looks the lease up and
reads its keys with no lock against the apply. A test would need to stop the apply between two
deletes of one revocation (a gofail point inside mvcc's delete, or a large lease whose revocation
takes long) while a `TimeToLive` with keys runs on the leader. The same partial set reaches
`checkLeaseRenew` and `checkLeaseTimeToLive`'s permission checks (a smaller cousin of
`issues/etcd-lease-timetolive-keys-toctou.md`).

**A second window: after a snapshot.** `applySnapshot` calls `lessor.Recover`, which loads the
snapshot's leases as fresh objects with empty key sets, then mvcc's `Restore`, which re-attaches the
snapshot's keys one `Attach` at a time (`server/storage/mvcc/kvstore.go:390-403`); a `TimeToLive`
with keys whose wait for the applied index ended just before the snapshot's apply began may list any subset of the keys attached at the snapshot's revision. Go usually
answers `ErrLeaderChanged` there (a fresh object's expiry is `forever`, so `Demoted()` is true,
`v3_server.go:662`), but not always: the lessor is not demoted by `Recover`, so a `Renew` of a loaded
lease on the leader refreshes its object's expiry, and `Demoted()` is then false.

## Proof

yes: W0's `leaseStep` (`SpecPlan/Spec/go_etcd_io/etcd/api/v3/Model.lean`, `.leaseTimeToLive`) says the keys
returned are exactly those attached at some revision `r`; the lessor's `Lease.Keys.spec` (batch 3c)
answers from a state of the lessor's history, which includes the states between two `Detach`es of
one entry. W0's step must allow, for an entry from revision `r` to `r'`, any set between
`attached(r) ∩ attached(r')` and `attached(r) ∪ attached(r')` (each key's membership changes at most
once in an entry: a transaction writes a key once), and, during a snapshot's restore, any subset
of the keys attached at the snapshot's revision; or 2c's `leaseTimeToLive` keeps a premise
(`req/go_etcd_io_etcd_api_v3.md`, "from 3c").

## Notes

Fix, if wanted: read the keys under the lessor's lock in a state the apply thread does not leave
half-done, e.g. take `le.mu` for the whole of a revocation's deletes, or answer `Keys` from mvcc's
store at the response's revision (a range over the keys whose record names the lease).
