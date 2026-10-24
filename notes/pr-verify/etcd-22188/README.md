# Reproduction and Probe Tests for `etcd-io/etcd#22188`

This directory contains the test probes and logs used in the verification of `etcd-io/etcd#22188` (`membership: don't panic in IsLocalMemberLearner when local member is absent`).

## Files

- [`cluster_pr22188_probe_test.go`](./cluster_pr22188_probe_test.go):
  - `TestIsLocalMemberLearner`: Tests all three branches of `(*RaftCluster).IsLocalMemberLearner()` (learner -> `true`, voting member -> `false`, removed/absent local member -> `false` without panicking, matching `IsLocalMemberLearner_present` and `IsLocalMemberLearner_absent`).
  - `TestUnaryInterceptorLearnerCheckRemovedMember`: Reproduces the race between `IsMemberExist(localID)` and `IsLocalMemberLearner()` when `RemoveMember(localID, ApplyBoth)` runs concurrently in the apply loop (`issues/etcd-unary-interceptor-learner-removed.md`).
  - `TestProbeRemovedLearnerReportedAsNonLearnerDuringShutdownWindow`: Demonstrates that when a **learner** member (`IsLearner == true`) is removed via `ConfChangeRemoveNode`, during the 1-second `stopWithDelay(10*100*time.Millisecond, ...)` window (`server.go:1225`) before `s.Stop()` runs, `IsLocalMemberLearner()` transitions from `true` to `false` ("report it as a non-learner"), causing `/readyz/non_learner` (`learnerCheck`) and the interceptor's `IsMemberExist && IsLearner` check to treat the unpromoted, removed learner as a non-learner.
- [`probe-test.log`](./probe-test.log): Output of running `go test -v` on the three tests above.

## How to Run

Copy `cluster_pr22188_probe_test.go` into `/root/etcd-pr/etcd-22188/server/etcdserver/api/membership/` and run:

```bash
cd /root/etcd-pr/etcd-22188/server
GOTOOLCHAIN=go1.27.1 go test -v -run 'TestIsLocalMemberLearner|TestUnaryInterceptorLearnerCheckRemovedMember|TestProbeRemovedLearnerReportedAsNonLearnerDuringShutdownWindow' ./etcdserver/api/membership
```
