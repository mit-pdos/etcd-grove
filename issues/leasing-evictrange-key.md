# clientv3/leasing: EvictRange evicts only the range's first key, leaving deleted keys in the cache

## Summary

`leaseCache.EvictRange(key, end)` in `client/v3/leasing` finds every cached key in `[key, end)` but deletes `key`, not the key it found, so a range evicts at most its first key. It is called when a range delete through the leasing KV returns an error; if the delete was applied by etcd anyway (a lost response, a timeout), the other cached keys in the range keep their deleted values, and later `Get`s through the leasing KV return them. I found this while formally verifying the leasing package.

## What happens

References are to `main` at f061acd0902d489041448cdd19d71a345d27b9f5.

1. `EvictRange` (`client/v3/leasing/cache.go:178-187`) loops over `lc.entries`, and for each `k` with `inRange(k, key, end)` runs `delete(lc.entries, key)` and `lc.revokes[key] = time.Now()` (`cache.go:183-184`): `key`, not `k`. The first key of the range is evicted (and marked revoked even if it was not cached); every other cached key in the range stays.
2. Its only caller is `deleteRangeRPC` (`client/v3/leasing/kv.go:340-351`): when the range-delete transaction (`If(CreateRevision(pfx+key).WithRange(pfx+end) < maxLeaseRev+1).Then(OpGet(key, WithRange(end), WithKeysOnly()), OpDelete(key, WithRange(end)))`) returns an error, it calls `EvictRange(key, end)` and returns the error. The error does not mean the transaction was not applied; the single-key delete handles the same case by evicting the key (`kv.go:393-395`, "don't know if delete was processed").
3. If the transaction was applied, the keys left in the cache hold values etcd has deleted. Nothing evicts them later: the transaction did not touch this client's leasing keys (`pfx+k`), so `monitorLease` (`kv.go:159-188`) sees no `REVOKE`. A `Get` of such a key through the leasing KV is served from the cache (`leaseCache.Get`, `cache.go:191-210`) and returns the deleted key, until another client writes the key (revoking this client's lease on it) or the leasing session ends.

## How to reproduce

The branch below adds:

- `TestLeaseCacheEvictRange`, `TestLeaseCacheEvictRangeBeginNotCached` and `TestLeaseCacheEvictRangeFromKey` (`client/v3/leasing/cache_test.go`), which cache some keys, call `EvictRange` and check that exactly the cached keys in the range are evicted and marked revoked. On `main` all three fail (e.g. with `a`, `b`, `c`, `d` cached, `EvictRange("a", "c")` leaves `b` cached).

  ```
  cd client/v3 && go test ./leasing/ -run EvictRange
  ```

- `TestLeasingOwnerDeleteRangeLostResponse` (`tests/integration/clientv3/lease/leasing_test.go`). The leasing KV's client has a gRPC unary interceptor that, once armed, lets the next range-delete `Txn` reach etcd and then returns `Unavailable` (not retried for a `Txn`), as if the response were lost. The test puts `a` and `b`, gets both through the leasing KV (caching them), deletes `[a, c)` through it (which returns the injected error), and checks that both keys are gone on etcd and that the leasing KV's `Get` returns neither. On `main`, the leasing KV returns `b` with its old value.

  ```
  cd tests && go test ./integration/clientv3/lease/ -run TestLeasingOwnerDeleteRangeLostResponse
  ```

No existing test exercised `EvictRange`; none needed changes.

## Expected

After a range delete through the leasing KV fails, no key in the range is served from the cache: every cached key in `[key, end)` is evicted (and marked revoked, so it is not re-acquired before the backoff), as the single-key delete does for its key.

## The fix

Branch `leasing-evictrange-key` (one commit, with the tests): `delete(lc.entries, k)` and `lc.revokes[k] = time.Now()`.
