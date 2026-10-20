---
upstream: unchecked
---

# server/etcdserver: a transaction with comparisons and no operations is served without a linearizable read

## Status

A bug in the read path (a linearizability violation of a public request), by code inspection; no
reproduction yet. A `Txn` whose `Success` and `Failure` lists are both empty (`Txn(ctx).If(cmps...)
.Commit()`, or `.Then()`/`.Else()` with no operations) is read-only and, vacuously, "serializable":
the server answers it from the member's local state without the read index, so its verdict
(`Succeeded`) and header revision can be stale, although the request asked for no serializable
read (the client cannot even say so: serializability is a property of a transaction's ranges).

## Where

At the pinned revision (`etc/goose.py`, etcd `8a24be2a324f`):

- `server/etcdserver/txn/txn.go:338-350`, `IsTxnSerializable`: `true` unless some operation of
  either branch is not a serializable range; for no operations at all, `true`.
- `server/etcdserver/v3_server.go:344-351`, `(*EtcdServer).Txn`: for a read-only transaction
  (`IsTxnReadonly`, likewise vacuously true), `LinearizableReadNotify` only if
  `!IsTxnSerializable(r)`; then the transaction runs on the local store.

The documentation of `Txn` (`api/etcdserverpb/rpc.proto`, the KV service) promises a
linearizable transaction unless its ranges are serializable; `clientv3.Txn` has no option for a
serializable comparison.

## What happens

A member that is behind (a follower that has not applied the latest entries, or a leader cut
off by a partition that has not yet stepped down) answers a compare-only transaction against its
old state: e.g. `If(Value(k) = "a")` succeeds after another client's `Put(k, "b")` returned, and
the reply's revision is older than the put's. A transaction with at least one non-serializable
range in either branch (or any write) is not affected: it takes the read index (or goes through
raft).

## Expected

A transaction is linearizable unless every one of its ranges asks to be serializable; one with
no ranges at all asks for nothing, so it should be linearizable (`IsTxnSerializable` false for
an empty transaction, or `Txn` taking the read index for it).

## How the proof handles it

The server's model has the same rule (`txn.txnSerializable`, `server/v3/etcdserver/txn/TxnRun.lean`;
`client_txn_end_to_end`'s read update only for `txnSerializable = false`), so a compare-only
transaction's reply carries no linearization point. `examples/linkvtxn`'s generator never makes
one (a multi-operation transaction has one to three operations, a compare-and-set a put and a
get), and `linkvtxn.Apply`'s input premise says so (`GenIn`,
`Proof/github_com/mit_pdos/etcd_grove/examples/linkvtxn/Calls.lean`).

## Possible fixes

`IsTxnSerializable` returns `false` when both lists are empty (a one-line guard), or `Txn` calls
`LinearizableReadNotify` for a read-only transaction with no operations. The first also changes
`IsTxnSerializable`'s other callers (the apply path's read-only fast path and its warnings), which
look unaffected.

## Found

2026-10-20, linkv-txn stage F (the linearizability instance over the robustness tester's KV
workload): the read-only transaction's case of `call`'s proof needs the read update, which the
client's end-to-end spec gives only for a transaction that is not serializable.
