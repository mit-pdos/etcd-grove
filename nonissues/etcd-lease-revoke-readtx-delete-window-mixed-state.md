---
upstream: none
checked: 2026-11-16
links:
  - etcd-io/etcd#17119 pr merged: related, not this behavior (the commit at `Unlock` when a delete is pending, which leaves the window below)
blocks-proof: no
---

# lease: a read transaction can see a lease revoke half applied (its keys deleted, its record still stored)

A backend read transaction that starts while `lessor.Revoke` finishes sees the revoke's key
deletions (the mvcc tombstones) but not the deletion of the lease's record from the `lease` bucket:
a state no step recorded (before the revoke: the record and the live key; after it: the tombstone and
no record).

**Why not an issue:** no etcd reader reads the `lease` bucket through a read transaction: the lessor
reads it only under the batch lock (`initAndRecover`, `schema.MustUnsafeGetAllLeases` over the batch
transaction, at boot and on `Recover`), and the lease APIs read the lessor's memory. The mvcc readers
read the `key` bucket only, where the revoke's effect is all puts. The test
(`etcd-lease-revoke-readtx-delete-window-mixed-state/`, copied into `server/storage/mvcc` at the fork
pin 6e8f0c004, go1.27.1) reads both buckets in one read transaction, which etcd does not do:

```
$ go test ./storage/mvcc/ -run TestLeaseRevokeReadWindowMixedState -count=1 -v
    zz_lease_revoke_window_test.go:86: reads 98, reads of an unrecorded state 4
--- FAIL: TestLeaseRevokeReadWindowMixedState (0.02s)
```

**How:** `lessor.Revoke` (`server/lease/lessor.go:326-365`) deletes the lease's keys through the mvcc
write transaction (tombstones: puts in `key`) and the record (`schema.UnsafeDeleteLease`, a delete in
`lease`) in one batch, ended by `txn.End()`. `batchTxBuffered.Unlock`
(`server/storage/backend/batch_tx.go:328-357`) writes the puts back into the read buffer, releases
`readTx`'s lock, then commits the delete. Same window as
[`etcd-membership-readtx-delete-window-mixed-state`](etcd-membership-readtx-delete-window-mixed-state.md).

## Proof

no: no trusted text promises a read transaction the `lease` bucket (`schema.MustUnsafeGetAllLeases`
and `lease.NewLessor` read under the batch lock, the writer's contents; `UnsafeDeleteLease` is a
write), and mvcc's reads of `key` are proved over the backend's proved read side, which has the
window (`notes/backend-delete-window-audit.md`).
