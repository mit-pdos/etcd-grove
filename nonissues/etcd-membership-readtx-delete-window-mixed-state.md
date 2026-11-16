---
upstream: none
checked: 2026-11-16
links:
  - etcd-io/etcd#17119 pr merged: related, not this behavior (the commit at `Unlock` when a delete is pending, which leaves the window below)
blocks-proof: no
---

# membership: a read of the member buckets can see a member removal half applied (removed and still a member)

A `MustReadMembersFromBackend` that runs while the apply thread finishes `MustDeleteMemberFromBackend`
returns the removed member both in the members map and in the removed map, a state no step
recorded (before the removal it is a member and not removed; after it, removed and not a member).

**Why not an issue:** no etcd caller reads the member buckets concurrently with a member removal:
`MustReadMembersFromBackend` is called by `bootstrap.go` (boot), `RaftCluster.Recover` (boot and
`applySnapshot`) and `ValidateConfigurationChange` (the apply thread, before the change is applied),
all on the thread that removes members, after the removal's `Unlock` (and its commit) returned. The
test reads from other goroutines, which etcd does not do. The test
(`etcd-membership-readtx-delete-window-mixed-state/`, copied into `server/storage/schema` at the fork
pin 6e8f0c004, go1.27.1):

```
$ go test ./storage/schema/ -run TestMembershipReadWindowMixedState -count=1 -v
    zz_membership_window_test.go:66: reads 91, reads of an unrecorded state 4 (first member 1)
--- FAIL: TestMembershipReadWindowMixedState (0.02s)
```

**How:** `MustDeleteMemberFromBackend` (`server/storage/schema/membership.go:73-81`) deletes
`members/<id>` and puts `members_removed/<id>` in one batch. `batchTxBuffered.Unlock`
(`server/storage/backend/batch_tx.go:328-357`) writes the put back into the read buffer under
`readTx.Lock()`, releases it, and only then commits the bbolt transaction holding the delete. A read
transaction (`readMembersFromBackend`, `membership.go:91-122`, `ReadTx().RLock()`) in between reads
`members_removed` from the read buffer (the new entry) and `members` from bbolt's last committed
snapshot (the member still there). The same window as
`etcd-auth-readtx-delete-window-mixed-state` (auth, on branch `auth-schema-srv`), [`etcd-lease-revoke-readtx-delete-window-mixed-state`](etcd-lease-revoke-readtx-delete-window-mixed-state.md)
and [`etcd-mvcc-compaction-readtx-delete-window-mixed-state`](etcd-mvcc-compaction-readtx-delete-window-mixed-state.md).

## Proof

no: the trusted `schema.membershipBackend.MustReadMembersFromBackend` takes the idle part of the
membership buckets (`backend.rbOwnIn d.γB membership.memberBkts bk`), which the removal's
`MustDeleteMemberFromBackend` axiom gives back only after its `Unlock` (commit included), and which
excludes any write session to those buckets while the read runs: no read is in the window
(`notes/backend-delete-window-audit.md`).

## Notes

A fix in etcd (not needed by etcd): keep `readTx` locked from the write-back through the commit when
a delete is pending.
