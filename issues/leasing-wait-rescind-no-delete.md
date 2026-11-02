---
upstream: none
checked: 2026-10-26
links:
  - etcd-io/etcd#20704 issue closed: related, not this bug (our leasing report, closed by the stale bot as not planned, unfixed; does not list this)
blocks-proof: no
---

# clientv3/leasing: a range delete goes through while another client still caches a key in the range

When a range delete through the leasing KV must revoke another leasing client's lease on a key and
the watch it waits on ends early (its start revision was compacted, or the client is closing), it
treats the lease as released and deletes the range anyway. The other client still holds its lease
and its cached `Get` keeps returning the deleted value.

**Expected:** a write through the leasing KV should commit only once no other leasing client
holds the lease on the key, which is the leasing protocol's rule ("the owner relinquishes its
exclusive access, permitting the writer to modify the key",
[doc](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/client/v3/leasing/doc.go#L36-L37)).

**Impact:** users of `client/v3/leasing` with two or more leasing clients on a prefix, a range or
prefix `Delete` of a key another client has cached, and a compaction (for example, the periodic
auto-compactor) past the revoke's revision while the delete waits; the other client then serves a
deleted key until its lease ends. Single-key writes only retry.

**Reproduction:** `TestLeasingDeleteRangeRevokeWatchCompacted` in
[`issues/leasing-wait-rescind-no-delete/leasing_revoke_watch_compacted_test.go`](leasing-wait-rescind-no-delete/leasing_revoke_watch_compacted_test.go),
copied into `tests/integration/clientv3/lease` at
etcd-io/etcd@1573d59416efa220421c451f5266b24a5d8374ef (2026-10-28), go1.27.3 (client B's watcher
compacts etcd before its first watch; client A's watcher is held until B watches again):

```
$ go test ./integration/clientv3/lease -run '^TestLeasingDeleteRangeRevokeWatchCompacted$' -count=1
--- FAIL: TestLeasingDeleteRangeRevokeWatchCompacted (0.23s)
        	Error:      	Should be empty, but was [key:"k"  create_revision:2  mod_revision:2  version:1  value:"v1"]
        	Messages:   	expected A's leasing KV not to return k, deleted on etcd, got [key:"k"  create_revision:2  mod_revision:2  version:1  value:"v1"]
FAIL
```

**Cause:** [`waitRescind`](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/client/v3/leasing/kv.go#L204-L216)
returns `ctx.Err()`, `nil` while the caller's context is live, when its watch channel closes
without the delete. [`revokeLeaseKvs`](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/client/v3/leasing/kv.go#L435-L451)
then returns a bound that covers the still-present leasing key, so
[`deleteRangeRPC`](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/client/v3/leasing/kv.go#L340-L352)'s
guard holds.

## Proof

no: the top-level adequacy proof needs no fix on the goosed fork for it; the leasing theorems take the leasing protocol as a premise (`LeasingProtocol`,
`Proof/go_etcd_io/etcd/client/v3/leasing/InvLeasingModel.lean`: no write to a key while another
client holds its lease), and this lets leasing clients break it; `waitRescind`'s spec has a third
outcome, `nil` with no promise. The verified fork carries no fix.

## Fix

**Branch**: `leasing-wait-rescind-no-delete` (upamanyus/etcd, pushed): d3db62afd test and fix (one commit)
**Base**: etcd-io/etcd@f061acd0902d489041448cdd19d71a345d27b9f5

**PR draft**:

Title: clientv3/leasing: keep waiting for a revoked lease when its watch ends

`waitRescind` waits for the leasing key that `revoke` just marked `"REVOKE"` to be deleted by its
holder: it watches the key from the revoke's revision + 1 and returns when it sees the delete. If
the watch channel closes first (its start revision was compacted, or the client is closing), it
returns `ctx.Err()`, which is nil while the caller's context is live. For a single-key Put or
Delete this costs a retry; for a range delete, `revokeLeaseKvs` returns the largest create
revision of the leasing keys, still-held ones included, and `deleteRangeRPC`'s guard holds: the
delete is applied while the other client still holds its lease.

This PR makes `waitRescind`, when the watch ends without the delete and the context is live, read
the leasing key: if it is gone, or was created after the revoke, the lease was released; otherwise
it watches again from the read's revision. A read error is returned. The integration test has a
client hold the lease on a key with its lease monitor stalled, and a second client delete a range
containing the key with a watcher that compacts etcd past the start revision of its first watch.

Alternative: return an error (`ErrRescindWatchClosed`) when the watch ends early; smaller, but it
surfaces a compaction, an ordinary event, as an error of the user's write.
