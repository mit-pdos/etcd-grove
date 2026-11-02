---
upstream: none
checked: 2026-11-02
links:
blocks-proof: yes
---

# etcdserver: a transaction nested about 5000 deep panics every member, permanently (with --max-txn-ops of 5000 or more)

With `--max-txn-ops` raised to about 5000 or more, one client `Txn` nested 4999 deep (each level a
transaction holding the next, the innermost one comparison; 34 KB on the wire) is accepted,
committed, and then panics the apply loop of every member with `unmarshal should never fail
(proto: exceeded maximum recursion depth)`. The entry is in every member's WAL, so a restarted
member replays it and panics again: the cluster stays down.

**Expected:** a request the server accepts and proposes should be applied; one too deep to be
applied should be refused before it is proposed.

**Impact:** only with a non-default `--max-txn-ops` of about 5000 or more (the default, 128,
limits the nesting to about 128 levels). Then any client allowed to send a `Txn` can take the
cluster down with one request; recovery means removing the entry from every member's WAL.

**Reproduction:** `TestTxnNestedDeep` in
[`issues/etcd-txn-nested-depth-apply-panic/txn_nested_depth_test.go`](etcd-txn-nested-depth-apply-panic/txn_nested_depth_test.go),
copied (as `zz_txn_nested_depth_test.go`) into `tests/integration/clientv3` at
etcd-io/etcd@a2e3642bcd2cca3a802503cdb09f64a3dc15cdf5 (2026-11-02), go1.27.3 (one member with
`MaxTxnOps: 10000`):

```
$ (cd tests && go test ./integration/clientv3 -run '^TestTxnNestedDeep$' -count=1)
panic: unmarshal should never fail (proto: exceeded maximum recursion depth) [recovered]
	panic: execute job failed
go.etcd.io/etcd/pkg/v3/pbutil.MustUnmarshalMessage(...)
	.../pkg/pbutil/pbutil.go:63 +0x94
go.etcd.io/etcd/server/v3/etcdserver/apply.Apply(...)
FAIL	go.etcd.io/etcd/tests/v3/integration/clientv3	0.266s
```

**Cause:** [`checkTxnRequest`](https://github.com/etcd-io/etcd/blob/a2e3642bcd2cca3a802503cdb09f64a3dc15cdf5/server/etcdserver/api/v3rpc/key.go#L202-L231)
bounds the nesting only through `--max-txn-ops` (each level is checked with the budget left by
its parent), and gRPC decodes requests up to protobuf-go's default depth of 10000 messages. A
4999-deep transaction is 10000 messages deep; the server wraps it in an `InternalRaftRequest`, one
level more, and the apply loop decodes each committed entry with
[`MustUnmarshalMessage`](https://github.com/etcd-io/etcd/blob/a2e3642bcd2cca3a802503cdb09f64a3dc15cdf5/server/etcdserver/apply/apply.go#L29),
which hits the same limit and
[panics](https://github.com/etcd-io/etcd/blob/a2e3642bcd2cca3a802503cdb09f64a3dc15cdf5/pkg/pbutil/pbutil.go#L61-L65).

## Proof

yes: it makes the property a top-level adequacy test over this code checks false for a workload such a test may use, and no fix is in the goosed fork yet; the proof sidesteps it: `proto.MarshalIRR.spec` takes the premise `apply.irrDepthOk` (the request at most 9999
messages deep, `Proof/go_etcd_io/etcd/server/v3/etcdserver/apply/IrrDepth.lean`), which the gRPC
handler discharges only under `NewServer.spec`'s configuration premise `v3rpc.maxTxnOpsOk`
(`--max-txn-ops` at most 4999, `Proof/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/RecvLimit.lean`);
etcd accepts any `--max-txn-ops`.

## Fix

Not written. Bound the nesting depth in `checkTxnRequest` (a depth parameter, a limit well below
5000 and independent of `--max-txn-ops`); or check before proposing that the marshalled request
decodes; decoding entries with a larger `RecursionLimit` only moves the boundary unless gRPC's
limit stays below it.

## Notes

A 5000-deep request is refused by gRPC (`codes.Internal`), harmlessly. A restart from the same
data directory panics again on replay (seen 2026-10-30 with the examples' `TestNestedDepthPoisonRestart`,
branch `axiom/txn-nested-wire`, since deleted; the test above was rebuilt from it). Related:
[`etcd-txn-keysonly-reply-alloc-panic`](etcd-txn-keysonly-reply-alloc-panic.md) and
[`nonissues/etcd-max-txn-ops-nested`](../nonissues/etcd-max-txn-ops-nested.md) (the same per-level
budget).
