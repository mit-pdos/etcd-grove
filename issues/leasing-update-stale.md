# clientv3/leasing: after a put of a cached key, the cache can hold a key-value etcd does not have

## Summary

After a `Put` (or a transaction's put) of a key it has cached, the leasing KV (`client/v3/leasing`) updates its cache with a key-value computed from the put's arguments, not the one etcd stores. That computed key-value is wrong in four cases:

1. a put with `WithIgnoreValue` caches the empty value;
2. a put with `WithLease` caches the key without the lease. Once the lease ends, etcd deletes the key, but the cache keeps returning it;
3. two concurrent puts whose responses arrive in the reverse order of their commits cache, in between, a version/value pair etcd never had;
4. a put and a delete whose responses arrive in the reverse order of their commits leave the put's value cached for a key etcd has deleted.

The cached `Get` returns these key-values. I found this while formally verifying the leasing package (the proofs characterize exactly when the update tracks etcd: only for a put that keeps the key's lease, with no `WithIgnoreValue`, applied in revision order).

## What happens

References are to `main` at f061acd0902d489041448cdd19d71a345d27b9f5.

After a successful put, `leasingKV.put` (`client/v3/leasing/kv.go:236-263`, line 250) and `txnLeasing.commitToCache` (`txn.go:159-179`, line 175) call `leaseCache.Update(key, op.ValueBytes(), header)` (`cache.go:132-152`):

- if the cached response has no key-value, it creates one with `CreateRevision` = the response's revision;
- it increments `Version` unconditionally;
- if `ModRevision < header.Revision`, it sets `ModRevision` and `Value` to the put's.

`Update` sees only the put's value bytes, so:

1. **`WithIgnoreValue`**: `op.ValueBytes()` is empty, so the cache stores `""`. etcd keeps the old value.
2. **`WithLease`**: the lease is not recorded, and a put without a lease does not clear a cached one. Worse, the key now has a lease. When the lease ends, etcd deletes the key, and nothing tells the cache: no leasing key changes, so no client revokes this one's lease. `acquire` refuses to cache keys that have a lease for exactly this reason (`kv.go:271-273`, `Compare(LeaseValue(key), "=", 0)`). The owner's put bypasses that check, and so does `acquire`'s already-owner path (`kv.go:282-286`), which re-caches the key after an eviction without looking at its lease.
3. **Out-of-order puts**: two puts by the same leasing KV commit at `r1 < r2`, and `r2`'s response is applied first. The cache then has `r2`'s value at the version `r1` left (one increment). etcd had `r1`'s value at that version, and `r2`'s value one version later. When `r1`'s response arrives, the version is incremented again and the value kept, so the final state matches etcd. Only a `Get` between the two responses sees the pair etcd never had.
4. **A put and a delete out of order**: a put commits at `r1` and a delete of the same key at `r2`, and the delete's response is applied first (`leaseCache.delete`, `cache.go:160-165`, clears the key-value). `Update` then finds no key-value and creates one with the put's value. The key stays cached as present until the lease is revoked or the session ends. This is the case of the earlier, non-deterministic `TestLeasingConcurrentPutDelete` on a fork (2025).

Concurrent writes of a key from one leasing KV are allowed: `leaseCache.Lock` only replaces the key's wait channel, it does not serialize writers.

## How to reproduce

The branch below adds these tests to `tests/integration/clientv3/lease/leasing_test.go`. Each compares the leasing KV's `Get` with a plain client's, and all of them fail on `main`:

| test | symptom | on `main` |
|---|---|---|
| `TestLeasingOwnerPutIgnoreValue` | 1 | the cached value is `""`, etcd has `"abc"` |
| `TestLeasingTxnOwnerPutIgnoreValue` | 1, through `Txn` | same |
| `TestLeasingOwnerPutWithLease` | 2 | the cached key has no lease; after a 3 s wait (past the eviction backoff) and after the lease is revoked, the leasing KV still returns the key, which etcd has deleted |
| `TestLeasingOwnerPutsOutOfOrder` | 3 | between the responses: value `"ghi"` at version 2, etcd has version 3 (after both, they agree) |
| `TestLeasingOwnerPutDeleteOutOfOrder` | 4 | after both: `key:"k" create_revision:4 mod_revision:4 version:1 value:"def"`; etcd has no `k` |

The two out-of-order tests are deterministic: the leasing KV's `cl.KV` is wrapped so that the first put's transaction, once committed, returns only after the second operation has returned.

```
cd tests && go test ./integration/clientv3/lease/ -run 'TestLeasingOwnerPut|TestLeasingTxnOwnerPutIgnoreValue' -v
```

No existing test encodes the old behaviour; the suite passes unchanged with the fix.

The other 2025 test, `TestLeasingConcurrentPutGet` (a `Put` whose response is lost through a partition, with a concurrent `Get`), concerns a write's unknown outcome, not `Update`. It is not covered here.

## Expected

The cache holds, for each key, a key-value etcd had at the cached revision, and never one that does not reflect a later write the client has seen. A key whose lease can delete it is not cached.

## The fix

Branch `leasing-update-stale` (one commit, with the tests). Rather than compute the new key-value, the leasing KV reads it in the same transaction as the put:

- `put` commits `Then(op, OpGet(key))`. `tryModifyOp` and `revoke` take the extra ops. A transaction's `serverTxn` appends an `OpGet` of every key it puts after the user's nested `OpTxn`. The user's responses are unchanged.
- `Update(key, kvs, header)` caches that read only if `header.Revision` is above the cached response's revision, which makes out-of-order responses no-ops. `Delete` already ignores an older response (`cache.go:161`).
- If the read shows a lease, `Update` evicts the key instead (marking it revoked, like `Evict`).
- `acquire`'s already-owner path does not count as acquired when the key has a lease, so the key is not re-cached after the backoff. This change is needed: without it, `TestLeasingOwnerPutWithLease` fails after the lease is revoked.

The read gives the exact key-value etcd has at the put's revision (value, lease, version, create revision), so the fix does not need to know the put's options. The leasing package cannot see them: `Op` has no exported accessors for `ignoreValue`, `ignoreLease` or the lease.

Alternatives:

- **`WithPrevKV`** on the put, with the response's `PrevKv` stripped when the user did not ask for it, as the 2025 fork attempt did. It gives the version and create revision, but not the value under `WithIgnoreValue` or the lease, without new `Op` accessors in `client/v3`. It also changes the user's nested transaction ops.
- **Evicting the key after every put.** That is simpler, but it gives up the cache for written keys during the 2 s revoke backoff.
