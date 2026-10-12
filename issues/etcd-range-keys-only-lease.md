# etcdserver: keys-only ranges return lease 0 unless sorted by value (regression in v3.7)

## Summary

Since 7624a8a2e ("Range with --keys-only retrieves from memory when possible", PR #21791, in v3.7.0), a keys-only range that is not sorted by value returns every key-value with `Lease` 0, even for a key attached to a lease. The same range sorted by value returns the lease. The API documents `keys_only` as returning the keys without the values, not as dropping the lease, and before 7624a8a2e every keys-only range returned it. I found this while formally verifying etcd's range execution.

## What happens

References are to `main` at f061acd0902d489041448cdd19d71a345d27b9f5.

1. `executeRange` (`server/etcdserver/txn/range.go:67`) sets `FastKeysOnly: r.KeysOnly && r.SortTarget != pb.RangeRequest_VALUE`.
2. With `FastKeysOnly`, `storeTxnCommon.rangeKeys` (`server/storage/mvcc/kvstore_txn.go:90-105`) builds the key-values from the in-memory index alone: key, mod and create revisions, version. The index does not record leases, so `Lease` is 0.
3. A keys-only range sorted by value takes the full read (the value is needed to sort), which decodes the stored key-value with its lease; `asembleRangeResponse` (`range.go:156`, `:166`) then clears only the value.
4. `keys_only` is documented as "when set returns only the keys and not the values" (`api/etcdserverpb/rpc.proto:486`).

So `etcdctl put --lease=<id> foo bar; etcdctl get foo --keys-only -w json` reports no lease for `foo`, and the same `get` with `--sort-by=VALUE` reports it. A client that reads keys-only to find which keys hold a lease (to check ownership, or to revoke or refresh it) sees none.

## How to reproduce

The branch below adds two tests:

- `TestRangeKeysOnlyLease` (`server/etcdserver/txn/txn_test.go`): keys `a` (lease 7) and `b` (lease 7, then put again without a lease); keys-only `Range` of each, sort target `KEY`, `VERSION` and `VALUE`, at the current revision and, for `b`, at the revision where it had the lease.
- `TestKVGetKeysOnlyLease` (`tests/integration/clientv3/kv_test.go`): grant a lease, put `foo` with it, `Get(ctx, "foo", clientv3.WithKeysOnly(), clientv3.WithSort(target, ...))` for the three sort targets; then put `foo` without the lease and `Get` keys-only at the leased revision.

```
cd server && go test ./etcdserver/txn/ -run TestRangeKeysOnlyLease -v
cd tests && go test ./integration/clientv3/ -run TestKVGetKeysOnlyLease -v
```

On `main`:

```
--- FAIL: TestRangeKeysOnlyLease/leased_key/KEY             expected: 7  actual: 0
--- FAIL: TestRangeKeysOnlyLease/leased_key/VERSION         expected: 7  actual: 0
--- FAIL: TestRangeKeysOnlyLease/lease_removed,_past_revision/KEY      expected: 7  actual: 0
--- FAIL: TestRangeKeysOnlyLease/lease_removed,_past_revision/VERSION  expected: 7  actual: 0
--- FAIL: TestKVGetKeysOnlyLease   expected: <lease id>  actual: 0   (sort by key and by version,
                                   at the current revision and at the leased revision)
```

The `VALUE` cases pass on `main`. No existing test encodes the lease-less behaviour; `go test ./server/etcdserver/txn/ ./server/storage/mvcc/`, `cd tests && go test ./integration/clientv3/ -run 'KeysOnly|Lease|Get'`, `./integration/clientv3/lease/` and `-tags integration ./common/ -run TestKVGet` pass with the fix.

## Expected

The same key-values whatever the sort target, with the lease the key had at the revision read, as before 7624a8a2e.

## The fix

Branch `range-keys-only-lease` (commit 01e522548, one commit off `main` f061acd09, with the tests). `executeRange` no longer sets `FastKeysOnly`: keys-only ranges read the key-values from the backend again and drop only the values. The mvcc option stays, with a comment that it returns no value and no lease (`server/storage/mvcc/kv.go`).

Filling the lease in the fast path from the lessor (`Lessor.GetLease`) was considered and rejected. Its lock order would be safe (mvcc reads and writes take the lessor's lock inside theirs, and the lessor never holds its lock while calling into mvcc: `Revoke` releases it before `le.rd()`, `lessor.go:326-343`). But the lessor gives the key's *current* lease, not its lease at the revision read. A range at a past revision then returns the wrong lease (the past-revision cases above fail with that fix), and a concurrent read can see a lease that a write in progress has attached or detached, with the key's old revision. The request does not say whether the caller needs the lease, so the fast path cannot be kept only for callers who don't. Keeping it would need the index to record leases, a larger change.

How the verification models the current behaviour: `notes/STATUS.md` (txn unit 2).
