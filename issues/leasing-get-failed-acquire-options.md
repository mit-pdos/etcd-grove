---
upstream: none
checked: 2026-10-26
links:
  - etcd-io/etcd#20704 issue closed: related, not this bug (our leasing report, closed by the stale bot as not planned, unfixed; does not list this)
blocks-proof: no
---

# clientv3/leasing: a Get of a key another client has leased ignores the request's options

When a `Get` through the leasing KV misses the cache and another leasing client holds the key's
lease, the leasing KV returns the result of a plain `Get` of the key instead of the caller's
request: `WithKeysOnly` returns the value, `WithCountOnly` returns the key-value, and revision
filters such as `WithMinModRev` are not applied.

**Expected:** a `Get` through the leasing KV should return what the same `Get` returns from etcd,
as the leasing KV is a [`clientv3.KV`](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/client/v3/leasing/doc.go#L15-L18)
serving linearizable reads.

**Impact:** users of `client/v3/leasing` (or the gRPC proxy with leasing) with two or more
leasing clients on one prefix, whose `Get`s use options; deterministic whenever the other client
holds the key's lease. A count-only or keys-only read returns more data than asked, and a revision
filter returns a key it should exclude.

**Reproduction:** `TestLeasingGetWithOptsNonOwner` in
[`issues/leasing-get-failed-acquire-options/leasing_get_opts_test.go`](leasing-get-failed-acquire-options/leasing_get_opts_test.go),
copied into `tests/integration/clientv3/lease` at
etcd-io/etcd@1573d59416efa220421c451f5266b24a5d8374ef (2026-10-28), go1.27.3:

```
$ go test ./integration/clientv3/lease -run '^TestLeasingGetWithOptsNonOwner$' -count=1
--- FAIL: TestLeasingGetWithOptsNonOwner (0.15s)
        	Messages:   	WithKeysOnly: value: leasing KV [key:"k" create_revision:2 mod_revision:2 version:1 value:"abc"], etcd [key:"k" create_revision:2 mod_revision:2 version:1]
        	Messages:   	WithCountOnly: Kvs: leasing KV [key:"k" create_revision:2 mod_revision:2 version:1 value:"abc"], etcd []
        	Messages:   	WithMinModRev: Kvs: leasing KV [key:"k" create_revision:2 mod_revision:2 version:1 value:"abc"], etcd []
FAIL
```

**Cause:** on a cache miss, [`leasingKV.get`](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/client/v3/leasing/kv.go#L323-L337)
calls `acquire(ctx, key, v3.OpGet(key))`, a plain get, not the caller's op. If the lease is
acquired, `leases.Add` applies the op's options to the cached response; if not
([`acquire`](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/client/v3/leasing/kv.go#L265-L299)'s
`Else` branch), `get` returns the plain get's response as is.

## Proof

no: the top-level adequacy proof needs no fix on the goosed fork for it; the leasing KV's intended spec is false here; the proof states what the code returns
(`getNotAcquired`, `Proof/go_etcd_io/etcd/client/v3/leasing/InvLeasingKV.lean`); the verified fork
carries no fix.

## Fix

**Branch**: `leasing-get-failed-acquire-options` (upamanyus/etcd, pushed): af95e2ff8 test and fix (one commit)
**Base**: etcd-io/etcd@f061acd0902d489041448cdd19d71a345d27b9f5

**PR draft**:

Title: clientv3/leasing: respect a Get's options when acquiring fails

When a Get misses the cache, `get` calls `acquire(ctx, key, v3.OpGet(key))`: a plain get of the
key, not the caller's op. If the lease is acquired, `leases.Add` applies the op's options to what it
returns; if another client holds the key's lease, `get` returns the plain get's response as is,
ignoring the options.

This PR makes `acquire`'s `Else` branch also run the caller's op (`Else(OpGet(key),
OpGet(pfx+key), op)`), and `get` returns its response when the lease is not acquired. Both branches
keep the plain get first, since the response cached is that get's: the `Else` branch also counts
as acquired when this client already holds the lease, and caching the op's response there would
cache a keys-only or count-only answer for later Gets. `acquire` has no other caller. The
integration test has one leasing KV hold the lease and gets the key through a second with
`WithKeysOnly`, `WithCountOnly` and `WithMinModRev`, comparing with a plain client's Get.
