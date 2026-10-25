# Reproduction and Probe Suite for `etcd-io/etcd#22122`

This directory contains the Go unit/probe tests and execution log accompanying the formal verification report [`../etcd-22122.md`](../etcd-22122.md).

## Files

- [`probe_test.go`](./probe_test.go): Go unit tests exercising `client/v3/ordering`:
  1. `TestPR22122_MutableTxnExecutedAtMostOnce`: Verifies that with PR `#22122`, a mutable transaction (`OpPut` in `Then`) executes `kv.KV.Do` **at most once** even when `txnResp.Header.Revision < prevRev` and `orderViolationFunc` returns `nil`.
  2. `TestPR22122_ReadOnlyNestedTxnRetriesUntilMonotonic`: Verifies that a read-only transaction (including a nested read-only `OpTxn`) retries on ordering violations until `txnResp.Header.Revision >= prevRev`.
  3. `TestCaveat1_MutableTxnViolationDiscardsCommittedRespWhenClosureErrors`: Demonstrates Caveat 1 — when `orderViolationFunc` returns a non-nil error (e.g. `ErrNoGreaterRev`), `txnOrdering.Commit()` has *already executed and committed* the mutable transaction on the server via `txn.KV.Do`, and then discards `txnResp` and returns `(nil, err)`.
  4. `TestCaveat2_PutDeleteAndDoBypassKvOrdering`: Demonstrates Caveat 2 — `kvOrdering` embeds `clientv3.KV` and only overrides `Get`, `GetStream`, and `Txn`, so `kv.Put`, `kv.Delete`, and `kv.Do` bypass `kvOrdering` completely without updating or checking `prevRev`.
- [`probe_test.log`](./probe_test.log): Output of running `go test -v ./ordering/...` on the Goose fork worktree `/root/etcd-pr/etcd-22122` (`pr-etcd-22122-goose-lean`, `767d327c5`).

## Running

```bash
cp notes/pr-verify/etcd-22122/probe_test.go /root/etcd-pr/etcd-22122/client/v3/ordering/probe_22122_test.go
cd /root/etcd-pr/etcd-22122/client/v3 && go test -v ./ordering/...
rm /root/etcd-pr/etcd-22122/client/v3/ordering/probe_22122_test.go
```
