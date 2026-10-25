# Reproduction Tests and Logs for `etcd-io/etcd#21401`

This directory contains standalone reproduction tests and test output logs for the verification of [`etcd-io/etcd#21401`](https://github.com/etcd-io/etcd/pull/21401) (`Experimenting with making debug log level useful for debugging linearizability issues`, head `afd8dffbf85a6db8ca001f3e4be003051f01bcd5`).

## Files

- [`repro_test.go`](./repro_test.go): Standalone Go test suite reproducing the bugs and hazards identified during formal verification in Lean/Iris:
  1. `TestReproBug1A_DuplicateRequestIDRegisterPanic`: Demonstrates that attaching `requestID := s.RequestID()` to the gRPC `ctx` in `newLogUnaryInterceptor` (`requestid.NewContext(ctx, requestID)`) and reusing `requestID := requestid.FromContext(ctx)` in `processInternalRaftRequestOnce` causes `s.w.Register(id)` (`wait.Wait`) to panic with `"dup id %x"` if two proposals overlap on the same `ctx`.
  2. `TestReproBug1B_SequentialProposalSameCtxCrossContaminatesApplyResult`: Demonstrates that sequential proposals on the same `ctx` (such as `EtcdServer.Authenticate`'s retry loop in `server/etcdserver/v3_server.go:853–887` or `quotaAlarmer.check` -> `s.Alarm(ctx, ...)` in `server/etcdserver/api/v3rpc/quota.go:48`) reuse the same `requestID` (even across child contexts `context.WithCancel(ctx)` / `context.WithTimeout(ctx)`). If an earlier proposal times out locally after `r.Propose` while still in flight in the Raft pipeline, its `applyAll` `s.w.Trigger(header.ID, res1)` delivers Proposal 1's stale `*apply.Result` to Proposal 2's waiter channel.
  3. `TestReproBug1C_V3ElectionCampaignResignTypeAssertionPanic`: Demonstrates that `v3election.electionServer.Campaign` (`server/etcdserver/api/v3election/election.go:40–92`, registered on the same gRPC server with `newLogUnaryInterceptor` and calling `v3client.New(s)` in-process on the caller's `ctx`) reuses the same `requestID` across multiple Raft proposals (`Txn` for `waitDeletes`/`Proclaim` and `DeleteRange` for `Resign`). If `Proclaim` (`Txn`) times out locally while in flight in Raft and `Campaign` calls `e.Resign(ctx)` (`DeleteRange`) on the same `ctx`, `s.w.Trigger(requestID, *pb.TxnResponse)` delivers `*pb.TxnResponse` to `DeleteRange`, causing `DeleteRange` (`v3_server.go:323`) to panic on `return resp.(*pb.DeleteRangeResponse), nil`.
  4. `TestReproBug2A_LogRaftCommunicationNilLoggerCrash`: Demonstrates that `logRaftCommunication(lg, ...)` dereferences `lg.Debug(...)` without checking `if lg == nil` (or `if p.tr != nil` / `if cr.tr != nil`), crashing when `lg == nil`.
  5. `TestReproBug2B_LogRaftCommunicationNilHeaderCrash`: Demonstrates that `logRaftCommunication` dereferences `r.Header.ID` on `raftpb.MsgProp` without checking `if r.Header != nil`, panicking with `SIGSEGV` when `r.Header == nil`.
  6. `TestReproBug3_InternalProposalTriggersWarnLog`: Demonstrates that all internal server background proposals (`publishV3`, `LeaseCheckpoint`, `corrupt.go` alarms, `DowngradeEnable`, `LinearizableReadNotify` outside unary gRPC interceptors) have `requestid.FromContext(ctx) == 0`, triggering `lg.Warn("RequestID not set in context when proposing, generating a new one")` on every internal proposal.
  7. `TestReproBug4_DuplicateSizeFieldInLogUnaryResponseStats`: Demonstrates that `logUnaryResponseStats` emits two `"size"` zap fields (`zap.Int("size", size)` in both `logUnaryResponseStats` and `getRangeResponseStatFields`).
- [`repro_test.log`](./repro_test.log): Output from running `go test -v ./...` on `repro_test.go` as well as `go test -v ./etcdserver/api/rafthttp -run '^(TestSendMessage|TestPipelineSend)$'` in `/root/etcd-pr/etcd-21401/server`, showing the actual `SIGSEGV` stack trace in `rafthttp.logRaftCommunication`.

## Running

```bash
cd notes/pr-verify/etcd-21401
go test -v ./...
```
