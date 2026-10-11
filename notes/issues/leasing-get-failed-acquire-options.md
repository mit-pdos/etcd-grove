# clientv3/leasing: a Get of a key leased by another client ignores the request's options

## Summary

When a `Get` through the leasing KV (`client/v3/leasing`) misses the cache and another client holds the key's lease, the leasing KV returns the response of a plain `Get` of the key instead of the caller's request: `WithKeysOnly` returns the value, `WithCountOnly` returns the key-value, and revision filters such as `WithMinModRev` are not applied. I found this while formally verifying the leasing package.

## What happens

References are to `main` at f061acd0902d489041448cdd19d71a345d27b9f5.

1. On a cache miss, `leasingKV.get` (`client/v3/leasing/kv.go:301-338`) calls `lkv.acquire(ctx, key, v3.OpGet(key))` (`kv.go:323`): a plain get of the key, not the caller's `op`.
2. `acquire` (`kv.go:265-299`) commits a transaction that runs that get in both branches: `Then(get, put leasing key with our lease)` if nobody holds the lease, `Else(get, get leasing key)` otherwise; in the `Else` case it reports `Succeeded` only if the leasing key is already ours (`kv.go:282-286`).
3. If the lease is acquired, `get` caches the plain get's response and `leases.Add(key, getResp, op)` (`cache.go:120-130`, through `leaseKey.get`, `cache.go:212-229`) applies `op`'s options to what is returned.
4. If it is not (another client holds the lease), `get` returns `resp.Responses[0]`, the plain get's response, as is (`kv.go:327-337`). The caller's options are never applied.

So, when another client holds the lease on `k = "abc"`:

| `Get("k", ...)` | leasing KV | etcd |
|---|---|---|
| `WithKeysOnly()` | `k = "abc"` | `k`, empty value |
| `WithCountOnly()` | `Kvs = [k = "abc"]`, `Count == 1` | no `Kvs`, `Count == 1` |
| `WithMinModRev(modRev+1)` | `Kvs = [k = "abc"]` | no `Kvs` |

## How to reproduce

The branch below adds `TestLeasingGetWithOptsNonOwner` (`tests/integration/clientv3/lease/leasing_test.go`): leasing KV A gets `k` (acquiring its lease), then leasing KV B gets `k` with each of `WithKeysOnly`, `WithCountOnly` and `WithMinModRev`, and the test compares B's `Count` and `Kvs` with a plain client's `Get` with the same option. On `main`:

```
WithKeysOnly: value: leasing KV [key:"k" create_revision:2 mod_revision:2 version:1 value:"abc"], etcd [key:"k" create_revision:2 mod_revision:2 version:1]
WithCountOnly: Kvs: leasing KV [key:"k" create_revision:2 mod_revision:2 version:1 value:"abc"], etcd []
WithMinModRev: Kvs: leasing KV [key:"k" create_revision:2 mod_revision:2 version:1 value:"abc"], etcd []
```

```
cd tests && go test ./integration/clientv3/lease/ -run TestLeasingGetWithOptsNonOwner -v
```

The existing `TestLeasingGetWithOpts` gets with options only from the client that holds the lease, which is served from the cache; it passes unchanged.

## Expected

A `Get` through the leasing KV returns what the same `Get` returns from etcd, whether or not the leasing KV acquires the key's lease.

## The fix

Branch `leasing-get-failed-acquire-options` (one commit, with the test). `get` passes its `op` to `acquire`, whose `Else` branch runs it after the plain get and the get of the leasing key (`Else(OpGet(key), OpGet(pfx+key), op)`); when the lease is not acquired `get` returns that third response. Both branches keep the plain get first because that is the response cached: the `Else` branch also counts as acquired when this client already holds the lease (e.g. two concurrent `Get`s of the same uncached key from one leasing KV), and caching the caller's response there (as `Else(op, OpGet(pfx+key))` would) would cache a keys-only or count-only answer for later `Get`s. `acquire` has no other caller.
