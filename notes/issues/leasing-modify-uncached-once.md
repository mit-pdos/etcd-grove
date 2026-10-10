# clientv3/leasing: a Put or Delete of a key the leasing KV has not cached is applied twice

## Summary

A `Put` or `Delete` through the leasing KV (`client/v3/leasing`) of a key it has not cached, when no other client holds the key's lease, is committed to etcd twice. A `Put` of a fresh key leaves it at version 2 with a mod revision one past its create revision, and `WithPrevKV` reports the put's own key-value as the previous one; a `Delete` of an existing key returns `Deleted == 0` and no `PrevKvs`, since the second delete finds nothing. I found this while formally verifying the leasing package.

## What happens

References are to `main` at f061acd0902d489041448cdd19d71a345d27b9f5.

1. `leasingKV.put` (`client/v3/leasing/kv.go:236-263`) and `leasingKV.delete` (`kv.go:380-411`) first call `tryModifyOp` (`kv.go:218-234`). It takes `wc, rev := lkv.leases.Lock(key)`, which is `(nil, 0)` when the key is not cached (`cache.go:53-61`), and commits `Txn().If(Compare(CreateRevision(pfx+key), "<", rev+1)).Then(op)`.
2. When no client holds the key's lease, the leasing key `pfx+key` does not exist, the comparison holds and `op` is applied. `tryModifyOp` returns `(resp, nil, nil)`: a successful response with a nil `wc`.
3. `put` and `delete` then test `if err != nil || wc == nil` (`kv.go:242`, `kv.go:390`) and call `revoke` (`kv.go:413-421`): a nil `wc` is taken to mean the commit did not happen. `revoke` commits `If(Compare(CreateRevision(pfx+key), "<", Rev(key)+1)).Then(op)` with `Rev(key) == 0` for the uncached key, the same guarded op, which succeeds again.
4. The response returned to the caller is the second commit's.

So for a fresh key `k`:

| through the leasing KV | etcd afterwards / returned | expected |
|---|---|---|
| `Put("k", "abc", WithPrevKV())` | version 2, mod revision = create revision + 1; `PrevKv` = `{k, "abc", version 1}` | version 1; `PrevKv == nil` |
| a second `Put("k", "def", WithPrevKV())` | version 4; `PrevKv.Value == "def"` (version 3) | version 2; `PrevKv.Value == "abc"` (version 1) |
| `Delete("k", WithPrevKV())` of a key put by another client | `Deleted == 0`, no `PrevKvs` | `Deleted == 1`, `PrevKvs[0].Value == "abc"` |

Each double put also generates two watch events and two revisions where one is expected.

## How to reproduce

The branch below adds two tests to `tests/integration/clientv3/lease/leasing_test.go`:

- `TestLeasingPutUncachedOnce` puts a fresh key through a leasing KV twice with `WithPrevKV` and checks the version and revisions (with a plain client's `Get`) and the previous key-values. On `main`:

  ```
  put of a fresh key returned a previous key-value: &mvccpb.KeyValue{Key:"k", CreateRevision:2, ModRevision:2, Version:1, Value:"abc"}
  version after one put: expected 1, actual 2
  mod revision after one put: expected 2, actual 3
  previous value of the second put: expected "abc", actual "def"
  previous version of the second put: expected 1, actual 3
  version after two puts: expected 2, actual 4
  ```

- `TestLeasingDeleteUncachedOnce` puts a key with the plain client and deletes it through a leasing KV with `WithPrevKV`. On `main`:

  ```
  number of keys deleted: expected 1, actual 0
  previous key-values of the delete: "[]" should have 1 item(s), but has 0
  ```

```
cd tests && go test ./integration/clientv3/lease/ -run 'TestLeasing(Put|Delete)UncachedOnce' -v
```

No existing leasing test encodes the double application (they put or delete cached keys, or do not check versions or `Deleted` on uncached ones); they pass unchanged with the fix.

## Expected

An operation through the leasing KV is applied once, as through a plain client.

## The fix

Branch `leasing-modify-uncached-once` (one commit, with the tests). `put` and `delete` call `revoke` only when `tryModifyOp` did not commit, i.e. `if err != nil || resp == nil`: `tryModifyOp` returns a nil response exactly when the transaction failed or did not succeed, and a nil `wc` with a response is a successful commit of an uncached key. The error path, including `delete`'s `Evict` on an error of `revoke`, is unchanged.
