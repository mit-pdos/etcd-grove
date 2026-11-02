---
upstream: none
checked: 2026-11-02
links:
  - etcd-io/etcd#11817 pr merged: related, where it starts (compactBarrier returns without closing the channel once the store is stopped, to fix a deadlock between Restore and a compaction)
  - etcd-io/etcd#10079 pr closed: related (an earlier attempt at the same deadlock)
blocks-proof: no
---

# mvcc: a physical compaction request hangs if the member installs a snapshot while its compaction waits behind another

A `Compact` request with `Physical` set (`etcdctl compaction --physical`,
`clientv3.WithCompactPhysical()`) waits until the member has finished deleting the compacted
revisions. If, on that member, the compaction is queued behind a running one and the member
installs a snapshot from the leader meanwhile (a follower that fell behind), the request never
returns: the member drops the queued compaction without telling the waiter, and the handler
goroutine leaks. The client sees its own deadline, or hangs without one.

**Expected:** a physical compaction request should return once the compaction is done or
abandoned, as it does when the snapshot interrupts the running compaction (whose waiter is
released).

**Impact:** low. It needs a physical compaction request, two compactions in flight on the same
member (a large store, whose compaction runs in batches with pauses, compacted again before it
finishes) and a snapshot installed on that member at that time. The store and the data are right;
only the request hangs and a goroutine leaks. The code is from #11817 (2021).

**Reproduction:** `TestRestoreDuringQueuedCompaction` in
[`issues/etcd-restore-pending-compaction-unclosed/restore_pending_compaction_test.go`](etcd-restore-pending-compaction-unclosed/restore_pending_compaction_test.go),
copied into `server/storage/mvcc` at etcd-io/etcd@a2e3642bcd2cca3a802503cdb09f64a3dc15cdf5
(2026-11-02), go1.27.3 (a store whose compaction pauses for an hour between batches of one key,
two `Compact` calls, then `Restore` as `applySnapshot` calls it):

```
$ (cd server && go test ./storage/mvcc -run '^TestRestoreDuringQueuedCompaction$' -count=1)
--- FAIL: TestRestoreDuringQueuedCompaction (5.15s)
    restore_pending_compaction_test.go:51: the channel of compaction 2 is not closed 5s after Restore
FAIL
```

**Cause:** [`store.Restore`](https://github.com/etcd-io/etcd/blob/a2e3642bcd2cca3a802503cdb09f64a3dc15cdf5/server/storage/mvcc/kvstore.go#L302-L307)
closes `stopc` and stops the scheduler, which [runs every pending job with a cancelled
context](https://github.com/etcd-io/etcd/blob/a2e3642bcd2cca3a802503cdb09f64a3dc15cdf5/pkg/schedule/schedule.go#L174-L184).
The queued compaction job then calls
[`compactBarrier`](https://github.com/etcd-io/etcd/blob/a2e3642bcd2cca3a802503cdb09f64a3dc15cdf5/server/storage/mvcc/kvstore.go#L137-L153)
with that context, which sees `stopc` closed and returns without closing the job's channel (its
comment assumes compaction and snapshot installation never overlap, which holds of the requests,
not of the compaction jobs). [`EtcdServer.Compact`](https://github.com/etcd-io/etcd/blob/a2e3642bcd2cca3a802503cdb09f64a3dc15cdf5/server/etcdserver/v3_server.go#L403-L404)
waits on that channel with no other case.

## Proof

no: the store's specs are partial correctness, and the model of a compaction's channel already
lets a receive return with the job abandoned (`compactDone`,
`Proof/go_etcd_io/etcd/server/v3/storage/mvcc/InvCompact.lean`); nothing claims the channel is
closed.

## Fix

Not written. In `compactBarrier`, close `ch` when `stopc` is closed instead of returning (nothing
waits for a later barrier once the store is stopped or restored); or have `EtcdServer.Compact` also
wait on `ctx.Done()` and `s.stopping`.
