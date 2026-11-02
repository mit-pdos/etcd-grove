---
upstream: none
checked: 2026-10-26
links:
  - etcd-io/etcd#20704 issue closed: related, not this bug (our leasing report, closed by the stale bot as not planned, unfixed; does not list this)
blocks-proof: yes
---

# clientv3/leasing: a transaction answered from the cache takes the wrong branch when it compares a missing key or a lease

A transaction through the leasing KV whose compared keys are all cached is answered from the cache,
and the cache evaluates comparisons differently from etcd: on a key cached as absent, `=` holds and
`<`, `>`, `!=` fail whatever the operand, and a `LeaseValue` comparison is never evaluated. For
example, after a `Get` of a missing key `k`, `Txn().If(Compare(CreateRevision("k"), "<", 5))`
reports `Succeeded == false` from the leasing KV and `true` from etcd, and runs the other branch.

**Expected:** a transaction through the leasing KV should report the `Succeeded` and run the
branch etcd would, as the leasing KV is a [`clientv3.KV`](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/client/v3/leasing/doc.go#L15-L18)
that "serves linearizable reads from a local cache".

**Impact:** users of `client/v3/leasing` (or the gRPC proxy with leasing) whose transactions
compare a key the leasing KV has cached as missing (any `Get` of a missing key caches it), or
compare `LeaseValue`, with a `Then`/`Else` of only `Get`s of cached keys. When the wrongly chosen
branch is all cached `Get`s, the transaction never reaches etcd, so the writes of the branch etcd
would have run are not sent (from reading the code; the test checks `Succeeded` only).

**Reproduction:** `TestLeasingTxnOwnerIfMissingKey` in
[`issues/leasing-evalcmp-missing-key/leasing_evalcmp_test.go`](leasing-evalcmp-missing-key/leasing_evalcmp_test.go),
copied into `tests/integration/clientv3/lease` at
etcd-io/etcd@1573d59416efa220421c451f5266b24a5d8374ef (2026-10-28), go1.27.3:

```
$ go test ./integration/clientv3/lease -run '^TestLeasingTxnOwnerIfMissingKey$' -count=1
--- FAIL: TestLeasingTxnOwnerIfMissingKey (0.27s)
        	Messages:   	CreateRevision("k") < 5 on a missing key: leasing KV Succeeded=false, etcd Succeeded=true
        	Messages:   	Version("k") = 3 on a missing key: leasing KV Succeeded=true, etcd Succeeded=false
        	Messages:   	Value("k") = "" on a missing key: leasing KV Succeeded=true, etcd Succeeded=false
FAIL
```

**Cause:** [`txnLeasing.eval`](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/client/v3/leasing/txn.go#L59-L89)
evaluates each comparison on the cached response with
[`evalCmp`](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/client/v3/leasing/util.go#L36-L71),
which computes `result` only when the key is present and has no `LEASE` case, so `result` stays 0.
etcd ([`applyCompare`, `compareKV`](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/server/etcdserver/txn/txn.go#L268-L336))
compares a missing key as the zero `KeyValue`, fails a `VALUE` comparison on it, and compares
`LEASE` against the key's lease.

## Proof

yes: it makes the property a top-level adequacy test over this code checks false for a workload such a test may use, and no fix is in the goosed fork yet; the proof sidesteps it: the leasing KV's intended spec (answers as etcd would) is false; the proof states what the
code computes (`leaseCmpHolds`, with the divergences `leasing_evalCmpM_absent_lt` and
`leasing_evalCmpM_lease`, `Proof/go_etcd_io/etcd/client/v3/leasing/Results.lean`); the
verified fork carries no fix.

## Fix

**Branch**: `leasing-evalcmp-missing-key` (upamanyus/etcd, pushed): 06541aec6 test and fix (one commit)
**Base**: etcd-io/etcd@f061acd0902d489041448cdd19d71a345d27b9f5

**PR draft**:

Title: clientv3/leasing: evaluate cached comparisons as etcd does

When every key compared by a transaction is cached and every op of the chosen branch is a cached
Get, `txnLeasing.eval` answers the transaction from the cache, evaluating each comparison with
`evalCmp`. `evalCmp` differs from etcd (`applyCompare` and `compareKV` in
`server/etcdserver/txn/txn.go`) in two ways: on a key cached as absent it compares nothing, so `=`
holds and `<`, `>`, `!=` fail whatever the target and operand, where etcd compares the zero
`KeyValue` (and fails a `VALUE` comparison); and it has no case for the `LEASE` target.

This PR compares a missing key as the zero `KeyValue`, fails a `VALUE` comparison on it, and adds the
`LEASE` case, as the server does. The unit test `TestEvalCmp` compares `evalCmp` with what etcd
computes for each target and result, on a missing and a present key; the integration test caches a
missing key and checks that the leasing KV's transaction succeeds exactly when the same
transaction does on etcd.

## Notes

The branch also has `TestEvalCmp` (`client/v3/leasing/util_test.go`, internal): 11 of its 31 cases
fail at the base, including the lease cases on a present key. Not filed: the leasing package is
lightly maintained (the 2026-10-18 ranking (`issues/INDEX.md`, in git history)); if filed, one umbrella issue for the leasing findings.
