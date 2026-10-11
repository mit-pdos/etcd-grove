# clientv3/leasing: a range delete can proceed while another client holds the lease on a key in the range

## Summary

When a write through the leasing KV (`client/v3/leasing`) must revoke another client's lease on a key, it waits for that client to delete its leasing key (`waitRescind`). If the watch it waits on ends without the delete (its start revision was compacted, or the client is closing), `waitRescind` returns `nil` as if the lease had been released. For a single-key write this only costs a retry. A range delete instead goes ahead while the other client still holds its lease, and that client's cached `Get`s keep returning the deleted value. I found this while formally verifying the leasing package.

## What happens

References are to `main` at f061acd0902d489041448cdd19d71a345d27b9f5.

1. `revoke` (`client/v3/leasing/kv.go:413-421`) commits `If(CreateRevision(pfx+key) < rev+1).Then(op).Else(OpPut(pfx+key, "REVOKE", WithIgnoreLease()))`. When another client holds the lease, the `Else` branch marks its leasing key, and `revoke` returns `waitRescind(ctx, key, resp.Header.Revision)`.
2. `waitRescind` (`kv.go:204-216`) watches `pfx+key` from that revision + 1 and returns `ctx.Err()` on the first delete event. If the watch channel closes first, the loop ends and it also returns `ctx.Err()`, which is `nil` while the caller's context is live. A watch whose start revision has been compacted is canceled by etcd and its channel closed. The same happens when the client is closing.
3. For a single-key `Put` or `Delete`, the caller retries `tryModifyOp`, whose guard fails again while the leasing key exists. So the retry is the only cost.
4. For a range delete, `revokeRange` → `revokeLeaseKvs` (`kv.go:423-451`) returns the largest create revision of the leasing keys in the range, still-held ones included. `deleteRangeRPC` (`kv.go:340-361`) then commits the delete guarded by `CreateRevision(pfx+key).WithRange(pfx+end) < maxLeaseRev+1`. That guard holds, since the still-present leasing key was created at or before `maxLeaseRev`. The delete is applied while the other client holds its lease.
5. The other client's cache still has the key. Its `monitorLease` (`kv.go:159-188`) rescinds only when it sees the `REVOKE` put, and if it has not yet seen it, its `Get` (`leaseCache.Get`, `cache.go:191-210`) returns the deleted value.

The leasing protocol rests on one invariant: no write to a key commits while another client holds the lease on it. Step 4 breaks it.

## How to reproduce

The branch below adds `TestLeasingDeleteRangeRevokeWatchCompacted` (`tests/integration/clientv3/lease/leasing_test.go`):

- Client A caches `k` through its leasing KV. A's watcher is gated, so its lease monitor does not run yet.
- Client B's watcher is wrapped. On the first watch it is asked for, it puts twice and compacts etcd at the new revision, so that watch is canceled (`ErrCompacted`). On a second watch, it opens A's gate.
- B runs `Delete("k", WithPrefix())` through its leasing KV.

On `main`, B's `waitRescind` returns `nil` after the first watch is canceled, and B's delete succeeds while A's leasing key still exists. A's `Get("k")` then returns `"v1"`, which etcd no longer has:

```
expected A's leasing KV not to return k, deleted on etcd, got [key:"k" create_revision:2 mod_revision:2 version:1 value:"v1"]
```

```
cd tests && go test ./integration/clientv3/lease/ -run TestLeasingDeleteRangeRevokeWatchCompacted -v
```

No existing test encodes the old behaviour; the suite passes unchanged with the fix.

## Expected

A write that revokes another client's lease proceeds only once that client's leasing key is gone. If the watch ends early, the wait goes on, or the write fails.

## The fix

Branch `leasing-wait-rescind-no-delete` (one commit, with the test). When the watch ends without the delete and the context is live, `waitRescind` reads the leasing key:

- if it is gone, or was created after the revoke (deleted and acquired again since), the lease was released and it returns `nil`;
- otherwise it watches again from the read's revision;
- a read error (for example, the client closing) is returned.

The alternative is to return an error, say `ErrRescindWatchClosed`, when the watch ends without the delete. That is a smaller change, and the range delete fails instead of proceeding. But it surfaces a compaction, an ordinary event, as an error of the user's `Put`, `Delete` or `Txn`, while the wait could simply go on. The read also matches what `monitorLease` does when its own watch ends (`kv.go:163-172`).
