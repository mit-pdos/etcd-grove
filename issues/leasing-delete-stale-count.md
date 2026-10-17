---
upstream: known
checked: 2026-10-16
links:
  - etcd-io/etcd#22417 issue open: this bug (reported by someone else), with the same reproduction and fix
  - etcd-io/etcd#22585 pr open: the fix (`li.response.Count = 0` in `leaseCache.delete`), verified on branch `pr-verify/etcd-22585` (`notes/pr-verify/etcd-22585.md`)
  - etcd-io/etcd#22507 pr open: the same one-line fix (byte-identical `cache.go`), with an integration test `TestLeasingDeleteCachedCount`; verified on branch `pr-verify/etcd-22507` (`notes/pr-verify/etcd-22507.md`)
---

# clientv3/leasing: a cached Get after a delete returns `Count == 1` with no key-values

## Status

A bug (a wrong result) in the verified code (`goose-lean` 09669450f): the leasing KV's cache
answers a `Get` of a key this client deleted with `Kvs == []` but the `Count` the key had when it
was cached (`1`), where etcd answers `Count == 0`. Not found by this repository's proofs: the
specs carried the cached `Count` through unchanged (`LeaseEntry.del` kept `count`) and no spec
related it to the key-values. Recorded while verifying the fix, etcd-io/etcd#22585.

## Where

`client/v3/leasing/cache.go:160-165` (`leaseCache.delete`) clears `li.response.Kvs` and sets the
header, but not `li.response.Count`; `leaseKey.get` (`cache.go:212`) answers from a copy of the
response's metadata (`copyGetResponseMetadataOnly`), `Count` included. `delete` is reached from
`leaseCache.Delete` (`leasingKV.delete`, `kv.go:366`, and `leasingKV.deleteRangeRPC`, `kv.go:411`)
and from `txnLeasing.commitToCache` (`txn.go:168,172`) for a transaction's deletes.

## What happens

```
lkv.Put("k", "v")       // the put caches k (Count 1)
lkv.Delete("k")         // the cached entry: Kvs = nil, Count still 1
lkv.Get("k")            // Kvs = [], Count = 1; etcd: Count = 0
```

The same after `lkv.Txn(ctx).Then(OpDelete("k")).Commit()`, and with `WithCountOnly()`.
Reproduction: `notes/pr-verify/etcd-22585/leasing_count_test.go`
(`tests/integration/clientv3/lease/`), `TestLeasingDeleteCount` and `TestLeasingTxnDeleteCount`,
which compare the leasing KV's `Count` with a plain client's: both fail on upstream `main`
d3c8a1559 and pass with etcd-io/etcd#22585 (`notes/pr-verify/etcd-22585/README.md`).

## Expected

`Count` is the number of keys in the range (etcd's `RangeResponse.count`): `0` for a deleted key.

## How the proof handles it

With etcd-io/etcd#22585 applied (branch `pr-verify/etcd-22585`), `LeaseEntry.del` sets the count
to `0` and every cache entry satisfies `LeaseEntry.countOk` (count = number of cached
key-values, `InvLeaseCache.lean`), part of `entryOwn`; `getCached`/`getAcquired`
(`InvLeasingKV.lean`) export it. On `lean` (the pinned code) the specs say nothing about the
count, so the bug is outside the verified results.

## Possible fixes

etcd-io/etcd#22585, or etcd-io/etcd#22507 (the same change to `cache.go`).

## Found

2026-10-16, verifying etcd-io/etcd#22585 (`.claude/skills/etcd-pr-verify`); reported upstream
before by etcd-io/etcd#22417.
