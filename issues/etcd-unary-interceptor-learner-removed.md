---
upstream: known
checked: 2026-11-01
links:
  - etcd-io/etcd#21966 issue open: same root cause (IsLocalMemberLearner panics after a concurrent removal), different caller (Maintenance/Status)
  - etcd-io/etcd#22188 pr open: same bug; returns false instead of panicking in IsLocalMemberLearner, names the unary/stream interceptors' non-atomic check; awaiting ok-to-test, no review
  - etcd-io/etcd#22205 pr open: same root cause, fix in IsLocalMemberLearner for #21966; needs rebase, does not mention the interceptor
  - etcd-io/etcd#21967 pr closed: same root cause, earlier fix attempt, closed unmerged
  - etcd-io/etcd#18606 pr merged: related, not this bug (the same check-then-act fixed for another caller, 3374e27f1)
blocks-proof: yes
---

# server: a request arriving as the member's own removal is applied can crash the member

A unary gRPC request whose interceptor finds the local member in the cluster, just before the apply
loop applies that member's removal, then asks whether the member is a learner: the member is gone, and
`IsLocalMemberLearner` panics (zap `Panic`, not recovered), killing the member instead of answering the
request or stopping cleanly. A narrow race on a member being removed.

**Reproduction:** `TestUnaryInterceptorLearnerCheckRemovedMember` in
[`issues/etcd-unary-interceptor-learner-removed/learner_removed_test.go`](etcd-unary-interceptor-learner-removed/learner_removed_test.go),
copied into `server/etcdserver/api/membership` at
etcd-io/etcd@1573d59416efa220421c451f5266b24a5d8374ef (2026-10-28), go1.27.3 linux/amd64. It runs, in
order, the interceptor's two calls
([`IsMemberExist(MemberID()) && IsLearner()`](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/server/etcdserver/api/v3rpc/interceptor.go#L53),
each under its own lock) with the apply loop's `RemoveMember` of the local member between them:

```
$ go test ./etcdserver/api/membership/ -run '^TestUnaryInterceptorLearnerCheckRemovedMember$' -count=1
    logger.go:146: ... PANIC	failed to find local ID in cluster members	{"cluster-id": "64", "local-member-id": "1"}
    learner_removed_test.go:37: the learner check of a request panicked: failed to find local ID in cluster members
FAIL
```

## Proof

yes: the verified fork carries #22188's fix (`c00a2dc06`, branch `goose-lean-learnerfix`: a removed
local member is no learner); before it, `EtcdServer.IsLearner`'s spec needed the premise
`membership.localKept` (`Spec/go_etcd_io/etcd/server/v3/etcdserver/api/membership/RaftCluster__IsLocalMemberLearner.lean`).

## Notes

The test plays the interleaving sequentially on the cluster object rather than racing a request
against a removal on a running member; upstream's fix of the same pattern for another caller
(3374e27f1) used the gofail failpoint `afterIsMemberExist` for an integration test.
