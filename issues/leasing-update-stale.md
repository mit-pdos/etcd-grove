---
upstream: reported
checked: 2026-11-01
links:
  - etcd-io/etcd#20704 issue closed: this bug for cases 3 and 4 (its bugs 3 and 1: Update increments Version, Update after Delete); cases 1-2 (WithIgnoreValue, WithLease) not in it; closed by the stale bot as not planned, unfixed
blocks-proof: no
---

# clientv3/leasing: after a put of a cached key, the leasing KV serves a key-value etcd does not have

After a `Put` (or a transaction's put) of a key it has cached, the leasing KV updates its cache
with a key-value computed from the put's arguments instead of the one etcd stores, and its `Get`
then returns that key-value. It is wrong in four cases: (1) a put `WithIgnoreValue` caches the empty
value; (2) a put `WithLease` caches the key without the lease, and once the lease ends and etcd
deletes the key, the cache keeps returning it; (3) two concurrent puts whose responses arrive in the
reverse order of their commits cache, in between, a version/value pair etcd never had; (4) a put and
a delete whose responses arrive in reverse order leave the put's value cached for a key etcd has
deleted. Cases 3 and 4 were reported in etcd-io/etcd#20704; cases 1 and 2 are not on GitHub.

**Reproduction:** five tests in
[`issues/leasing-update-stale/leasing_update_stale_test.go`](leasing-update-stale/leasing_update_stale_test.go)
(`TestLeasingOwnerPutIgnoreValue`, `TestLeasingTxnOwnerPutIgnoreValue`: case 1;
`TestLeasingOwnerPutWithLease`: case 2; `TestLeasingOwnerPutsOutOfOrder`: case 3;
`TestLeasingOwnerPutDeleteOutOfOrder`: case 4, the last two holding the first put's response
until the second operation returned), copied into `tests/integration/clientv3/lease` at
etcd-io/etcd@1573d59416efa220421c451f5266b24a5d8374ef (2026-10-28), go1.27.3; each compares the
leasing KV's `Get` with a plain client's (`-etcd +leasing`):

```
$ go test ./integration/clientv3/lease -run '^TestLeasing(OwnerPut|TxnOwnerPutIgnoreValue)' -count=1
--- FAIL: TestLeasingOwnerPutIgnoreValue (0.21s)
    leasing_update_stale_test.go:51: leasing KV's "k" differs from etcd's (-etcd +leasing):
        - 		"value":        []uint8("abc"),
--- FAIL: TestLeasingOwnerPutWithLease (3.22s)
    leasing_update_stale_test.go:76: leasing KV's "k" differs from etcd's (-etcd +leasing):
        - 		"lease":           int64(9063108962769662215),
    leasing_update_stale_test.go:84: leasing KV's "k" differs from etcd's (-etcd +leasing):
        - 	nil,
        + 	{s`key:"k"  create_revision:2  mod_revision:4  version:2  value:"def"`},
--- FAIL: TestLeasingTxnOwnerPutIgnoreValue (0.20s)
        - 		"value":        []uint8("abc"),
--- FAIL: TestLeasingOwnerPutsOutOfOrder (0.17s)
    leasing_update_stale_test.go:143: leasing KV's "k" differs from etcd's (-etcd +leasing):
          		"value":        []uint8("ghi"),
        - 		"version":      int64(3),
        + 		"version":      int64(2),
--- FAIL: TestLeasingOwnerPutDeleteOutOfOrder (0.23s)
    leasing_update_stale_test.go:187: leasing KV's "k" differs from etcd's (-etcd +leasing):
        - 	nil,
        + 	{s`key:"k"  create_revision:4  mod_revision:4  version:1  value:"def"`},
FAIL
```

**Cause:** `put` and `txnLeasing.commitToCache` call
[`leaseCache.Update(key, op.ValueBytes(), header)`](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/client/v3/leasing/cache.go#L132-L152),
which increments the version unconditionally and sets the value to the op's bytes (no lease) if the
response is newer than the cached mod revision; it never sees the put's options or etcd's result.

## Proof

no: the top-level adequacy proof needs no fix on the goosed fork for it; the leasing KV's intended spec is false here; the proof characterizes when `Update` tracks
etcd (`leasing_update_tracks_put`) and states the divergences (`leasing_update_ignoreValue`,
`leasing_update_out_of_order`, `Proof/go_etcd_io/etcd/client/v3/leasing/Results.lean`); the
verified fork carries no fix.

## Fix

**Branch**: `leasing-update-stale` (upamanyus/etcd, pushed): d97e455c2 test and fix (one commit)
**Base**: etcd-io/etcd@f061acd0902d489041448cdd19d71a345d27b9f5

The put reads the key in the same transaction (`Then(op, OpGet(key))`; a transaction's
`serverTxn` appends an `OpGet` of every key it puts), and `Update` caches that read only if its
revision is above the cached one (out-of-order responses become no-ops); a key read back with a
lease is evicted instead, and `acquire`'s already-owner path does not count a key with a lease as
acquired.

## Notes

One root cause (the cache computes the key-value instead of reading it), two triggers: put options
(cases 1-2, unreported) and response order (cases 3-4, #20704). If the leasing findings are filed
again, as one umbrella issue with small PRs (the 2026-10-18 ranking (`issues/INDEX.md`, in git history)), cases 1-2 could be a file of their own.
