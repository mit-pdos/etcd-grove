---
upstream: known
checked: 2026-11-01
links:
  - etcd-io/etcd#21869 pr closed: same bug and fix (delete k, not key, in EvictRange); closed unmerged by serathius citing the AI-contribution policy
  - etcd-io/etcd#21589 pr closed: same bug and fix, bundled with a lease-freshness fix for #19091; closed unmerged by its author
  - etcd-io/etcd#20704 issue closed: related, not this bug (our leasing report, closed by the stale bot as not planned, unfixed; does not list this)
blocks-proof: yes
---

# clientv3/leasing: after a failed range delete, the leasing KV keeps serving keys etcd deleted

When a range delete through the leasing KV returns an error although etcd applied it (a lost
response, a timeout), only the range's first key is evicted from the cache; the other cached keys
in the range keep their deleted values, and later `Get`s through the leasing KV return them until
another client writes them or the session ends.

**Reproduction:** `TestLeasingOwnerDeleteRangeLostResponse` in
[`issues/leasing-evictrange-key/leasing_evictrange_test.go`](leasing-evictrange-key/leasing_evictrange_test.go),
copied into `tests/integration/clientv3/lease` at
etcd-io/etcd@1573d59416efa220421c451f5266b24a5d8374ef (2026-10-28), go1.27.3 (a client interceptor
returns `Unavailable` after the range delete's `Txn` reached etcd):

```
$ go test ./integration/clientv3/lease -run '^TestLeasingOwnerDeleteRangeLostResponse$' -count=1
--- FAIL: TestLeasingOwnerDeleteRangeLostResponse (0.23s)
        	Error:      	Should be empty, but was [key:"b" create_revision:4 mod_revision:4 version:1 value:"v"]
        	Messages:   	expected the leasing KV not to return "b", deleted on etcd, got [key:"b" create_revision:4 mod_revision:4 version:1 value:"v"]
FAIL
```

**Cause:** [`leaseCache.EvictRange`](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/client/v3/leasing/cache.go#L178-L187)
loops over the cached keys `k` in the range but deletes `key`, not `k`; its only caller is
[`deleteRangeRPC`](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/client/v3/leasing/kv.go#L340-L351)'s
error path.

## Proof

yes: it makes the property a top-level adequacy test over this code checks false for a workload such a test may use, and no fix is in the goosed fork yet; the proof sidesteps it: the leasing KV's intended spec (linearizable reads) is false after such an error; the proof
states what the code does (`LeaseCacheSt.evictRange`,
`Proof/go_etcd_io/etcd/client/v3/leasing/leaseCache__EvictRange.lean`); the verified fork carries
no fix.

## Fix

**Branch**: `leasing-evictrange-key` (upamanyus/etcd, pushed): 14d1c4bf3 test and fix (one commit)
**Base**: etcd-io/etcd@f061acd0902d489041448cdd19d71a345d27b9f5

`delete(lc.entries, k)` and `lc.revokes[k] = time.Now()`, as #21869 did. The branch also has
internal unit tests of `EvictRange` (`client/v3/leasing/cache_test.go`).
