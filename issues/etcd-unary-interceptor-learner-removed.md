---
upstream: known
checked: 2026-10-16
links:
  - etcd-io/etcd#21966 issue open: same root cause (IsLocalMemberLearner panics after concurrent removal), different caller (Maintenance/Status)
  - etcd-io/etcd#22188 pr open: same bug; returns false instead of panicking in IsLocalMemberLearner, names the unary/stream interceptors' non-atomic check; awaiting ok-to-test, no review
  - etcd-io/etcd#22205 pr open: same root cause, fix in IsLocalMemberLearner for #21966; needs rebase, does not mention the interceptor
  - etcd-io/etcd#21967 pr closed: same root cause, earlier fix attempt, closed unmerged
  - etcd-io/etcd#18606 pr merged: related, not this bug (the same check-then-act fixed for another caller, 3374e27f1)
---

# server: the unary interceptor's learner check panics if the local member is removed meanwhile

- **Status**: open (a narrow race: a reachable panic of a member that is being removed).
- **Where**: `server/etcdserver/api/v3rpc/interceptor.go` at the pinned revision
  (`etc/goose.py`, bc8b52a50319): `newUnaryInterceptor`'s
  `s.IsMemberExist(s.MemberID()) && s.IsLearner() && !isRPCSupportedForLearner(req)`;
  `server/etcdserver/server.go` `EtcdServer.IsLearner` (`s.cluster.IsLocalMemberLearner()`);
  `server/etcdserver/api/membership/cluster.go:786` `RaftCluster.IsLocalMemberLearner`, which
  calls `c.lg.Panic("failed to find local ID in cluster members")` when `c.members` has no entry
  for `c.localID`; `IsMemberExist` and `IsLocalMemberLearner` each lock the cluster, so the
  conjunction is not atomic.
- **What happens**: a gRPC unary request whose interceptor finds the local member in the cluster
  (`IsMemberExist`), after which the apply loop applies the local member's removal
  (`applyConfChange`, `RemoveMember`; the server stops only afterwards), reaches
  `IsLocalMemberLearner` with the member gone: the server panics (zap's `Panic`), instead of
  answering the request or stopping. Reproduction of the interleaving, sequentially (in
  `server/etcdserver/api/membership`; passes: the panic is caught):

  ```go
  func TestUnaryInterceptorLearnerCheckRemovedMember(t *testing.T) {
  	c := newTestCluster(t, []*Member{newTestMember(1, nil, "node1", nil), newTestMember(2, nil, "node2", nil)})
  	c.SetID(types.ID(1), types.ID(100))
  	if !c.IsMemberExist(types.ID(1)) {
  		t.Fatal("local member should exist")
  	}
  	// the apply loop applies the local member's removal here
  	c.RemoveMember(types.ID(1), true)
  	defer func() {
  		if r := recover(); r == nil {
  			t.Fatal("expected IsLocalMemberLearner to panic")
  		}
  	}()
  	c.IsLocalMemberLearner()
  }
  ```

  (`IsLocalMemberLearner panicked: failed to find local ID in cluster members`.)
- **How it happens**: every unary gRPC request passes the learner check in
  `newUnaryInterceptor`. The check first asks whether the local member exists, then whether it
  is a learner. Each call takes the cluster lock separately, so the member can be removed in
  between, and `IsLocalMemberLearner` panics if the local member is missing:

  1. Member 1 serves a unary request (a `Put`, say). The interceptor calls
     `s.IsMemberExist(1)`: true.
  2. The apply loop applies the conf change that removes member 1: `RemoveMember(1)` deletes
     it from `c.members`. The server stops only after the apply.
  3. The interceptor calls `s.IsLearner()`, which calls `IsLocalMemberLearner`. `c.members` has
     no entry for `c.localID`, so it calls `c.lg.Panic`. Nothing recovers panics in etcd's gRPC
     handlers, so the process dies.

  Upstream fixed the same check-then-act pattern for another caller in 3374e27f1 (2024,
  "etcdserver: fix panic when checking IsLearner of removed member"), with the failpoint
  `afterIsMemberExist` to test it. The interceptor still has the pattern.

  ```go
  // server/etcdserver/api/v3rpc/interceptor.go:53-55 and api/membership/cluster.go:786-797 (etcd main f061acd09)
  		if s.IsMemberExist(s.MemberID()) && s.IsLearner() && !isRPCSupportedForLearner(req) { // <-
  			return nil, rpctypes.ErrGRPCNotSupportedForLearner
  		}
  // cluster.go
  func (c *RaftCluster) IsLocalMemberLearner() bool {
  	c.Lock()
  	defer c.Unlock()
  	localMember, ok := c.members[c.localID]
  	if !ok {
  		c.lg.Panic( // <-
  			"failed to find local ID in cluster members",
  			zap.String("cluster-id", c.cid.String()),
  			zap.String("local-member-id", c.localID.String()),
  		)
  	}
  	return localMember.IsLearner
  ```
- **Expected**: the learner check of a request is a check, not a crash: a removed member answers
  (an error, as it does when `IsMemberExist` is already false) or stops.
- **How the proof handles it**: `EtcdServer.IsLearner`'s spec (an axiom: `server.go` and
  `membership` are names-only, `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__IsLearner.lean`)
  has the premise `membership.localKept c` (an axiomatized predicate,
  `Proof/go_etcd_io/etcd/server/v3/etcdserver/api/membership/Defs.lean`: the local member stays
  in the members map), a premise of `newUnaryInterceptor`'s spec
  (`Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/newUnaryInterceptor.lean`) and so of the
  interceptor contract the server's gRPC result `etcd_kv_served` takes
  (`Proof/go_etcd_io/etcd/client/v3/Results.lean`).
- **Possible fixes**: one locked check (`RaftCluster.IsLocalMemberLearner` returning
  `(isLearner, ok bool)`, or a `RaftCluster.IsMemberLearner(id) (bool, bool)` the interceptor
  calls once); or `IsLocalMemberLearner` returning `false` for a missing local member instead of
  panicking.
- **Found**: 2026-10-14, unit P3b (the server's unary interceptor proved), by the spec of
  `IsLearner` needing the local member present.
