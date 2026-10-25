# Reproduction & Probe Suite for `etcd-io/etcd#18680`

This directory contains the standalone Go test suite (`repro_test.go`) and its captured output (`repro_test.log`) used in the formal verification report [`notes/pr-verify/etcd-18680.md`](../etcd-18680.md).

## Contents

- [`repro_test.go`](repro_test.go):
  1. `TestIssue18667_RemoveNeedlessRangeReqs_RevisionInconsistency`: Reproduces issue `etcd-io/etcd#18667` where `removeNeedlessRangeReqs` strips `RequestRange` ops on followers (`needResult == false`) prior to `checkTxn`, causing followers to commit writes when the leader rejects the transaction with `mvcc.ErrFutureRev`, and verifies that PR `#18680` (`apply.Apply` with `SkipRangeExecution: false`) preserves consistency across leader and followers.
  2. `TestIssue18667_RemoveNeedlessRangeReqs_AuthBypassInconsistency`: Reproduces the RBAC authorization bypass caused by `removeNeedlessRangeReqs` when Auth is enabled (`authApplierV3.Txn` -> `CheckTxnAuth`), where stripping `RequestRange` on followers (`needResult == false`) allows an unauthorized write in a mixed `[Range, Put]` transaction to commit on followers while the leader rejects the transaction with `auth.ErrPermissionDenied`, and verifies that PR `#18680` rejects the transaction on both leader and followers.
  3. `TestMainSkipRangeExecution_InvalidSortTargetAsymmetry_FixedByPR18680`: Demonstrates the remaining leader-vs-follower asymmetry on `main` (`SkipRangeExecution: !needResult && raftReq.Txn != nil`) identified by the Lean proof of `executeTxn` (`GetOk`: `validSortTarget o`), where an invalid `SortTarget` in a `RequestRange` inside a write `Txn` passes `checkRange` (`range.go:174–184`), panics the leader (`SkipRangeExecution == false`) in `sortRangeResults` (`range.go:145`) before `txnWrite.End()`, and commits the write on followers (`SkipRangeExecution == true`), whereas PR `#18680` (`SkipRangeExecution: false`) makes leader and follower execution identical.
  4. `TestCheckRangeVsRangeKeys_NegativeRevisionAfterCompaction`: Demonstrates the discrepancy between standalone `txn.Range` (`mvcc.rangeKeys`: `if rev <= 0 { rev = curRev }`) and `txn.Txn`'s `checkRange` (`case req.Revision == 0: ... case req.Revision < rv.FirstRev(): return mvcc.ErrCompacted`) for negative `Revision` (`-1`) after compaction.
- [`repro_test.log`](repro_test.log): Output of running the test suite.

## How to Run

From the `/root/etcd-pr/etcd-18680/server` directory:

```bash
cp /shared/etcd-grove-pr/etcd-18680/notes/pr-verify/etcd-18680/repro_test.go ./etcdserver/apply/repro_18680_test.go
GOTOOLCHAIN=go1.27.1 go test -v -run "TestIssue18667|TestMainSkipRangeExecution|TestCheckRangeVsRangeKeys" ./etcdserver/apply
rm -f ./etcdserver/apply/repro_18680_test.go
```
