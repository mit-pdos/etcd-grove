# Reproduction and Probe Artefacts for `etcd-io/etcd#19809`

This directory contains the Go probe tests and execution log for [`etcd-io/etcd#19809`](https://github.com/etcd-io/etcd/pull/19809) (`Combine common txn arguments into TxnContext`, head commit `23baf839b39e565f1933ea6c76bfb18f948fa93c`).

## Files

- [`txn_context_probe_test.go`](txn_context_probe_test.go): Go unit and behavioral probe tests for `server/etcdserver/apply` and `server/etcdserver/txn`:
  - `TestPR19809_ApplierV3Backend_ContextAndOps`: Verifies `(*applierV3backend).context()` construction and end-to-end execution of `Put`, `Range`, `Txn`, and `DeleteRange` through `applierV3backend`.
  - `TestPR19809_RangeAndDeleteRangeIgnoreUnusedTxnContextFields`: Demonstrates that `txn.Range` and `txn.DeleteRange` never access `TxnContext.Lessor` or `TxnContext.TxnModeWriteWithSharedBuffer` (passing a `Lessor` that panics on any method invocation and toggling `TxnModeWriteWithSharedBuffer` has no effect).
  - `TestPR19809_EtcdServerRangeFeatureGateEvaluation`: Demonstrates that `(*EtcdServer).Range` (`server/etcdserver/v3_server.go`) now evaluates `s.Cfg.ServerFeatureGate.Enabled(features.TxnModeWriteWithSharedBuffer)` (performing an interface dispatch, `atomic.Value.Load()`, and map lookup) on every `Range` call even though `txn.Range` ignores `TxnModeWriteWithSharedBuffer`.
- [`test.log`](test.log): Output of running `GOTOOLCHAIN=go1.27.1 go test -v -count=1 -run TestPR19809 ./etcdserver/apply`.

## Running

Copy `txn_context_probe_test.go` into `server/etcdserver/apply/` in the `pr-etcd-19809-goose-lean` worktree (`/root/etcd-pr/etcd-19809`) and run:

```bash
cd /root/etcd-pr/etcd-19809/server
GOTOOLCHAIN=go1.27.1 go test -v -count=1 -run TestPR19809 ./etcdserver/apply
```
