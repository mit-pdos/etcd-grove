---
upstream: none
checked: 2026-11-01
links:
  - etcd-io/etcd#20418 issue closed: stale reads from a paused process (robustness); different cause
blocks-proof: yes
---

# etcdserver: a Txn with comparisons and no operations returns a stale result from a member that is behind

A `Txn` with comparisons and no operations (`Txn(ctx).If(cmps...).Commit()`) is answered from the
member's local state without the read index, so a member that is behind (a follower that has not
applied the latest writes, or a leader cut off by a partition) returns a stale verdict and revision:
`If(Version("foo") = 0)` succeeds at revision 1 after a put of `foo` returned at revision 2.

**Expected:** such a txn should be linearizable, as the same txn with a `Get` is: the
[`RangeRequest`](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/api/etcdserverpb/rpc.proto#L478-L484)
documentation says ranges are linearizable unless `serializable` is set, and a txn without
operations has no range that asked for it (`clientv3.Txn` has no way to ask).

**Impact:** any cluster, default configuration, for clients that send compare-only transactions
(e.g. to test a condition) to a member that is behind; a linearizability violation of the verdict
and header revision. Rare in practice: most txns carry an operation. All v3 releases
(`IsTxnSerializable` has been vacuously true for an empty txn since 2016).

**Reproduction:** `TestTxnCompareOnlyLinearizable` in
[`issues/etcd-txn-empty-serializable/txn_compare_only_test.go`](etcd-txn-empty-serializable/txn_compare_only_test.go),
copied (as `zz_txn_compare_only_test.go`) into `tests/integration/clientv3` at
etcd-io/etcd@1573d59416efa220421c451f5266b24a5d8374ef (2026-10-28), go1.27.3; a follower partitioned
from the other two members answers after a put through the leader returned:

```
$ (cd tests && go test ./integration/clientv3 -run '^TestTxnCompareOnlyLinearizable$' -count=1)
--- FAIL: TestTxnCompareOnlyLinearizable (0.32s)
    zz_txn_compare_only_test.go:48:
        	Error:      	"1" is not greater than or equal to "2"
        	Test:       	TestTxnCompareOnlyLinearizable
        	Messages:   	txn answered without the put (succeeded: true)
FAIL
```

**Cause:** for a read-only txn, `EtcdServer.Txn` takes the read index only if `!IsTxnSerializable(r)`
([v3_server.go#L345-L352](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/server/etcdserver/v3_server.go#L345-L352));
`IsTxnSerializable` is true unless some operation is not a serializable range
([txn.go#L338-L350](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/server/etcdserver/txn/txn.go#L338-L350)),
so it is true for a txn with no operations.

## Proof

yes: the server's model has the same rule, so a compare-only txn's reply carries no linearization
point, and the linearizability result of `examples/linkvtxn` takes the premise that the workload
sends none (`GenIn`, `Proof/github_com/mit_pdos/etcd_grove/examples/linkvtxn/Calls.lean`).

## Fix

**Branch**: `fix/etcd-txn-empty-serializable` in `~/etcd-fixes/etcd-txn-empty-serializable` (upamanyus/etcd, not pushed): bf3c1135b test, e3010762c fix
**Base**: etcd-io/etcd@7ff040cb84c9944d0c38a9f0dc9f12ed9c58223b

**PR draft**:

Title: etcdserver: serve a txn without operations linearizably

[`Txn`](https://github.com/etcd-io/etcd/blob/7ff040cb84c9944d0c38a9f0dc9f12ed9c58223b/server/etcdserver/v3_server.go#L345-L352) skips the read index for a read-only txn when [`IsTxnSerializable`](https://github.com/etcd-io/etcd/blob/7ff040cb84c9944d0c38a9f0dc9f12ed9c58223b/server/etcdserver/txn/txn.go#L338-L350) holds, assuming that the client asked for a serializable read. `IsTxnSerializable` checks only that every operation is a serializable range, so it holds for a txn without operations, which asks for no serializable read although its comparisons read keys. This PR makes `IsTxnSerializable` false for a txn without operations.

The first commit adds a test of the issue's example, which fails on `main`; the second, the fix, makes it pass.

**If a reviewer asks**: fixing the caller instead (`|| no ops` in `Txn`) leaves the helper wrong for
the next caller; `IsTxnReadonly`, also vacuously true, is right (no writes). A nested txn op is
neither a range nor read-only, so such txns already go through raft. Cost: a compare-only txn now
waits for the read index; a client wanting the old local answer can add a serializable `Get`.
