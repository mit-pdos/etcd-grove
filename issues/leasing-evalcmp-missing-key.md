---
upstream: none
checked: 2026-10-26
links:
  - etcd-io/etcd#20704 issue closed: related, not this bug (the user's leasing report, closed by the stale bot as not planned, unfixed; does not list this)
---

# clientv3/leasing: transactions answered from the cache evaluate comparisons on missing keys and leases differently from etcd

## Summary

The leasing KV answers a transaction from its cache when all compared keys are cached and the chosen branch has only cached `Get`s. Its comparison function, `evalCmp` in `client/v3/leasing/util.go`, does not evaluate comparisons as etcd does: on a key cached as absent it compares nothing (so `=` holds and `<`, `>`, `!=` fail whatever the operand), and it ignores the `LEASE` target. The leasing KV's transaction then reports the wrong `Succeeded` and runs the wrong branch, while the same transaction on etcd takes the other one. For example, after a `Get` of a missing key `k` through the leasing KV, `Txn().If(Compare(CreateRevision(k), "<", 5)).Then(OpGet(k))` returns `Succeeded == false` from the leasing KV and `true` from etcd. I found this while formally verifying the leasing package.

## What happens

References are to `main` at f061acd0902d489041448cdd19d71a345d27b9f5.

1. `txnLeasing.Commit` (`client/v3/leasing/txn.go:52-57`) first tries `eval` (`txn.go:59-89`), which calls `leaseCache.evalCmp` (`client/v3/leasing/cache.go:257-271`) on the comparisons; if every compared key is cached it evaluates each with `evalCmp(lk.response, cmp)` and, if the chosen branch's ops are all cached `Get`s (`evalOps`, `cache.go:273-295`), returns the result without contacting etcd.
2. A `Get` of a missing key through the leasing KV acquires the key's lease and caches the empty response (`leasingKV.get`, `kv.go:323-336`; `leaseCache.Add`), so a missing key is cached as absent.
3. `evalCmp` (`util.go:36-71`) only computes `result` when `len(resp.Kvs) != 0` (`util.go:38`); for a missing key `result` stays 0. Its target switch (`util.go:41-58`) has no `Compare_LEASE` case, so for a lease comparison `result` also stays 0.

   ```go
   // client/v3/leasing/util.go:36-60 (etcd main f061acd09)
   func evalCmp(resp *v3.GetResponse, tcmp v3.Cmp) bool {
   	var result int
   	if len(resp.Kvs) != 0 { // <- a missing key: result stays 0
   		kv := resp.Kvs[0]
   		cmp := tcmp.GetCompare()
   		switch cmp.GetTarget() {
   		case v3pb.Compare_VALUE:
   		// ... the VALUE, CREATE and MOD cases, as VERSION ...
   		case v3pb.Compare_VERSION:
   			if tv, _ := cmp.GetTargetUnion().(*v3pb.Compare_Version); tv != nil {
   				result = compareInt64(kv.Version, tv.Version)
   			}
   		} // <- no Compare_LEASE case
   	}
   	switch tcmp.GetCompare().GetResult() {
   ```
4. etcd (`applyCompare` and `compareKV`, `server/etcdserver/txn/txn.go:268-336`) compares a missing key as the zero `KeyValue` (create and mod revision, version and lease 0), except that a `VALUE` comparison on a missing key always fails (`txn.go:278-284`), and compares `LEASE` with `compareInt64(ckv.Lease, rev)` (`txn.go:319-323`).

   ```go
   // server/etcdserver/txn/txn.go:278-285, 319-323 (etcd main f061acd09)
   	if len(rr.KVs) == 0 {
   		if c.Target == pb.Compare_VALUE {
   			// Always fail if comparing a value on a key/keys that doesn't exist;
   			// nil == empty string in grpc; no way to represent missing value
   			return false
   		}
   		return compareKV(c, &mvccpb.KeyValue{}) // <-
   	}
   	// ... in compareKV:
   	case pb.Compare_LEASE:
   		if tv, _ := c.TargetUnion.(*pb.Compare_Lease); tv != nil {
   			rev = tv.Lease
   		}
   		result = compareInt64(ckv.Lease, rev)
   ```

So, on a key cached as absent:

| comparison | etcd | leasing cache |
|---|---|---|
| `CreateRevision(k) < 5` | true (0 < 5) | false |
| `CreateRevision(k) != 5` | true | false |
| `Version(k) = 3` | false | true |
| `Value(k) = ""` | false (value of a missing key) | true |
| `LeaseValue(k) = 7` | false | true |

and on a cached key with lease 7, `LeaseValue(k) = 8` and `LeaseValue(k) > 6` give true/false where etcd gives false/true, since `result` is 0 for every lease comparison.

The transaction then returns the wrong `Succeeded` and the wrong branch's responses. When the branch the cache wrongly picks has only cached `Get`s, the transaction never reaches etcd, so the writes of the branch etcd would have run are never sent. For example, `Txn().If(Compare(CreateRevision(k), "<", 5)).Then(OpPut(k, v)).Else(OpGet(k))` on a key `k` cached as absent returns `Succeeded == false` with the cached `Get`, and puts nothing; etcd would have put `k`. (This consequence is from reading the code, `eval` and `evalOps` at `txn.go:59-89` and `cache.go:273-295`; no test runs it.)

## How to reproduce

The branch below adds:

- `TestEvalCmp` (`client/v3/leasing/util_test.go`), a table of comparisons on a missing and on a present key (every target, every result), each with the value etcd computes. On `main`, 11 of its 31 cases fail (the missing-key cases that differ, and the lease cases on the present key).

  ```
  cd client/v3 && go test ./leasing/ -run TestEvalCmp -v
  ```

- `TestLeasingTxnOwnerIfMissingKey` (`tests/integration/clientv3/lease/leasing_test.go`), which gets the missing key `k` through a leasing KV (caching it as absent) and then, for `CreateRevision("k") < 5`, `Version("k") = 3` and `Value("k") = ""`, commits `Txn().If(cmp).Then(OpGet("k"))` through the leasing KV and through the plain client, and checks that both report the same `Succeeded`. On `main`:

  ```
  CreateRevision("k") < 5 on a missing key: leasing KV Succeeded=false, etcd Succeeded=true
  Version("k") = 3 on a missing key: leasing KV Succeeded=true, etcd Succeeded=false
  Value("k") = "" on a missing key: leasing KV Succeeded=true, etcd Succeeded=false
  ```

  ```
  cd tests && go test ./integration/clientv3/lease/ -run TestLeasingTxnOwnerIfMissingKey -v
  ```

The existing leasing tests (`TestLeasingTxnOwnerIf` and the rest) compare only present keys on value, revisions and version; they pass unchanged.

## Expected

A transaction answered from the cache returns the same `Succeeded` and branch as etcd would for the cached state.

## The fix

Branch `leasing-evalcmp-missing-key` (one commit, with the tests). `evalCmp` keeps its shape and mirrors the server: a missing key is compared as the zero `KeyValue`, a `VALUE` comparison on it returns false, and a `LEASE` case compares `kv.Lease` with the operand's lease.
