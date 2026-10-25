// Copyright 2026 The etcd Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

package apply_test

import (
	"context"
	"testing"
	"time"

	"github.com/stretchr/testify/require"
	"go.uber.org/zap/zaptest"
	"golang.org/x/crypto/bcrypt"
	"google.golang.org/protobuf/proto"

	"go.etcd.io/etcd/api/v3/authpb"
	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/pkg/v3/pbutil"
	"go.etcd.io/etcd/pkg/v3/traceutil"
	"go.etcd.io/etcd/pkg/v3/wait"
	"go.etcd.io/etcd/server/v3/auth"
	"go.etcd.io/etcd/server/v3/etcdserver/api/membership"
	"go.etcd.io/etcd/server/v3/etcdserver/api/v3alarm"
	"go.etcd.io/etcd/server/v3/etcdserver/apply"
	"go.etcd.io/etcd/server/v3/etcdserver/cindex"
	"go.etcd.io/etcd/server/v3/etcdserver/txn"
	"go.etcd.io/etcd/server/v3/lease"
	"go.etcd.io/etcd/server/v3/storage/backend"
	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
	"go.etcd.io/etcd/server/v3/storage/mvcc"
	"go.etcd.io/etcd/server/v3/storage/schema"
	"go.etcd.io/raft/v3/raftpb"
)

type testNode struct {
	b    backend.Backend
	kv   mvcc.WatchableKV
	as   auth.AuthStore
	ua   apply.UberApplier
	w    wait.Wait
}

func newTestNode(t *testing.T) *testNode {
	return newTestNodeOpt(t, true)
}

func newTestNodeNoClose(t *testing.T) *testNode {
	return newTestNodeOpt(t, false)
}

func newTestNodeOpt(t *testing.T, closeOnCleanup bool) *testNode {
	t.Helper()
	lg := zaptest.NewLogger(t)
	b, _ := betesting.NewDefaultTmpBackend(t)
	if closeOnCleanup {
		t.Cleanup(func() { betesting.Close(t, b) })
	}

	ci := cindex.NewConsistentIndex(b)
	schema.CreateMetaBucket(b.BatchTx())
	lessor := lease.NewLessor(lg, b, nil, lease.LessorConfig{MinLeaseTTL: 5})
	kv := mvcc.New(lg, b, lessor, mvcc.StoreConfig{})
	if closeOnCleanup {
		t.Cleanup(func() { kv.Close() })
	}

	tp, err := auth.NewTokenProvider(lg, "simple", func(_ uint64) <-chan struct{} {
		ch := make(chan struct{})
		close(ch)
		return ch
	}, time.Minute)
	require.NoError(t, err)
	as := auth.NewAuthStore(lg, schema.NewAuthBackend(lg, b), tp, bcrypt.MinCost)
	alarmStore, err := v3alarm.NewAlarmStore(lg, schema.NewAlarmBackend(lg, b))
	require.NoError(t, err)

	ua := apply.NewUberApplier(apply.ApplierOptions{
		Logger:               lg,
		KV:                   kv,
		Lessor:               lessor,
		AlarmStore:           alarmStore,
		AuthStore:            as,
		ConsistentIndex:      ci,
		TxnModeWriteWithSharedBuffer: false,
		Backend:              b,
		QuotaBackendBytesCfg: 100 * 1024 * 1024,
		WarningApplyDuration: time.Second,
	})
	return &testNode{
		b:  b,
		kv: kv,
		as: as,
		ua: ua,
		w:  wait.New(),
	}
}

// legacyRemoveNeedlessRangeReqs is the pre-#18680 function from server/etcdserver/server.go.
func legacyRemoveNeedlessRangeReqs(rt *pb.TxnRequest) {
	f := func(ops []*pb.RequestOp) []*pb.RequestOp {
		j := 0
		for i := 0; i < len(ops); i++ {
			if _, ok := ops[i].Request.(*pb.RequestOp_RequestRange); ok {
				continue
			}
			ops[j] = ops[i]
			j++
		}
		return ops[:j]
	}
	rt.Success = f(rt.Success)
	rt.Failure = f(rt.Failure)
}

func mustMarshalEntry(t *testing.T, raftReq *pb.InternalRaftRequest) *raftpb.Entry {
	t.Helper()
	data, err := proto.Marshal(raftReq)
	require.NoError(t, err)
	return &raftpb.Entry{Data: data}
}

func countKey(t *testing.T, kv mvcc.KV, key string) int64 {
	t.Helper()
	n, err := txn.Count(context.Background(), zaptest.NewLogger(t), kv, []byte(key), nil, 0)
	require.NoError(t, err)
	return n
}

// TestIssue18667_RemoveNeedlessRangeReqs_RevisionInconsistency reproduces issue #18667:
// Under legacy removeNeedlessRangeReqs, a write Txn containing a Range op with a future
// revision (Revision: 999) fails with ErrFutureRev on the leader (needResult=true),
// leaving "k2" unwritten, whereas on a follower (needResult=false) removeNeedlessRangeReqs
// strips the Range op before checkTxn, so checkTxn succeeds and the follower writes "k2"!
// Under PR #18680 (apply.Apply with SkipRangeExecution=false), both leader and follower
// reject the Txn with ErrFutureRev and remain consistent.
func TestIssue18667_RemoveNeedlessRangeReqs_RevisionInconsistency(t *testing.T) {
	lg := zaptest.NewLogger(t)
	reqID := uint64(42)
	makeEntry := func() *raftpb.Entry {
		raftReq := &pb.InternalRaftRequest{
			Header: &pb.RequestHeader{ID: reqID},
			Txn: &pb.TxnRequest{
				Success: []*pb.RequestOp{
					{
						Request: &pb.RequestOp_RequestRange{
							RequestRange: &pb.RangeRequest{
								Key:      []byte("k1"),
								Revision: 999, // future revision
							},
						},
					},
					{
						Request: &pb.RequestOp_RequestPut{
							RequestPut: &pb.PutRequest{
								Key:   []byte("k2"),
								Value: []byte("foo"),
							},
						},
					},
				},
			},
		}
		return mustMarshalEntry(t, raftReq)
	}

	// 1. Legacy pre-#18680 behavior: leader rejects, follower commits "k2"="foo"!
	leaderLegacy := newTestNode(t)
	followerLegacy := newTestNode(t)

	_ = leaderLegacy.w.Register(reqID)
	arLeader, _ := apply.Apply(lg, makeEntry(), leaderLegacy.ua, leaderLegacy.w, membership.ApplyBoth)
	require.ErrorIs(t, arLeader.Err, mvcc.ErrFutureRev)
	require.Equal(t, int64(0), countKey(t, leaderLegacy.kv, "k2"), "leader must not write k2")

	// Follower (needResult=false) running legacy removeNeedlessRangeReqs before uberApply.Apply:
	var followerReq pb.InternalRaftRequest
	pbutil.MustUnmarshalMessage(&followerReq, makeEntry().Data)
	legacyRemoveNeedlessRangeReqs(followerReq.Txn)
	arFollowerLegacy := followerLegacy.ua.Apply(&apply.InternalRaftRequestWrapper{
		InternalRaftRequest: &followerReq,
	}, membership.ApplyBoth)
	require.NoError(t, arFollowerLegacy.Err)
	require.Equal(t, int64(1), countKey(t, followerLegacy.kv, "k2"),
		"BUG #18667: follower with removeNeedlessRangeReqs silently wrote k2 while leader rejected Txn!")

	// 2. PR #18680 behavior via apply.Apply: both leader (waiter registered) and follower (no waiter)
	// reject the Txn with ErrFutureRev and neither writes "k2".
	leaderFixed := newTestNode(t)
	followerFixed := newTestNode(t)

	_ = leaderFixed.w.Register(reqID)
	arLeaderFixed, _ := apply.Apply(lg, makeEntry(), leaderFixed.ua, leaderFixed.w, membership.ApplyBoth)
	arFollowerFixed, _ := apply.Apply(lg, makeEntry(), followerFixed.ua, followerFixed.w, membership.ApplyBoth)
	require.ErrorIs(t, arLeaderFixed.Err, mvcc.ErrFutureRev)
	require.ErrorIs(t, arFollowerFixed.Err, mvcc.ErrFutureRev)
	require.Equal(t, int64(0), countKey(t, leaderFixed.kv, "k2"))
	require.Equal(t, int64(0), countKey(t, followerFixed.kv, "k2"))
}

// TestIssue18667_RemoveNeedlessRangeReqs_AuthBypassInconsistency demonstrates that
// pre-#18680 removeNeedlessRangeReqs also bypassed RBAC CheckTxnAuth on followers:
// when user "alice" has WRITE permission on "k2" but NO READ permission on "secret",
// a Txn with [Range("secret"), Put("k2", "pwned")] is rejected with ErrPermissionDenied
// on the leader (needResult=true), whereas on followers (needResult=false)
// removeNeedlessRangeReqs stripped Range("secret") before authApplierV3.Txn ran
// CheckTxnAuth, so followers allowed the unauthorized write to "k2"!
func TestIssue18667_RemoveNeedlessRangeReqs_AuthBypassInconsistency(t *testing.T) {
	lg := zaptest.NewLogger(t)
	setupAuth := func(n *testNode) uint64 {
		_, err := n.as.UserAdd(&pb.AuthUserAddRequest{Name: "root", Options: &authpb.UserAddOptions{NoPassword: true}})
		require.NoError(t, err)
		_, err = n.as.RoleAdd(&pb.AuthRoleAddRequest{Name: "root"})
		require.NoError(t, err)
		_, err = n.as.UserGrantRole(&pb.AuthUserGrantRoleRequest{User: "root", Role: "root"})
		require.NoError(t, err)

		_, err = n.as.UserAdd(&pb.AuthUserAddRequest{Name: "alice", Options: &authpb.UserAddOptions{NoPassword: true}})
		require.NoError(t, err)
		_, err = n.as.RoleAdd(&pb.AuthRoleAddRequest{Name: "writer-k2-only"})
		require.NoError(t, err)
		_, err = n.as.RoleGrantPermission(&pb.AuthRoleGrantPermissionRequest{
			Name: "writer-k2-only",
			Perm: &authpb.Permission{
				PermType: authpb.Permission_WRITE,
				Key:      []byte("k2"),
			},
		})
		require.NoError(t, err)
		_, err = n.as.UserGrantRole(&pb.AuthUserGrantRoleRequest{User: "alice", Role: "writer-k2-only"})
		require.NoError(t, err)
		require.NoError(t, n.as.AuthEnable())
		return n.as.Revision()
	}

	leader := newTestNode(t)
	follower := newTestNode(t)
	authRev := setupAuth(leader)
	require.Equal(t, authRev, setupAuth(follower))

	reqID := uint64(77)
	makeEntry := func() *raftpb.Entry {
		raftReq := &pb.InternalRaftRequest{
			Header: &pb.RequestHeader{
				ID:           reqID,
				Username:     "alice",
				AuthRevision: authRev,
			},
			Txn: &pb.TxnRequest{
				Success: []*pb.RequestOp{
					{
						Request: &pb.RequestOp_RequestRange{
							RequestRange: &pb.RangeRequest{Key: []byte("secret")},
						},
					},
					{
						Request: &pb.RequestOp_RequestPut{
							RequestPut: &pb.PutRequest{Key: []byte("k2"), Value: []byte("pwned")},
						},
					},
				},
			},
		}
		return mustMarshalEntry(t, raftReq)
	}

	// Leader (needResult=true): rejects with ErrPermissionDenied, "k2" not written.
	_ = leader.w.Register(reqID)
	arLeader, _ := apply.Apply(lg, makeEntry(), leader.ua, leader.w, membership.ApplyBoth)
	require.ErrorIs(t, arLeader.Err, auth.ErrPermissionDenied)
	require.Equal(t, int64(0), countKey(t, leader.kv, "k2"))

	// Legacy follower (removeNeedlessRangeReqs before uberApply.Apply): strips Range("secret")
	// before CheckTxnAuth, so CheckTxnAuth succeeds and "k2" is written!
	var legacyFollowerReq pb.InternalRaftRequest
	pbutil.MustUnmarshalMessage(&legacyFollowerReq, makeEntry().Data)
	legacyRemoveNeedlessRangeReqs(legacyFollowerReq.Txn)
	arLegacyFollower := follower.ua.Apply(&apply.InternalRaftRequestWrapper{
		InternalRaftRequest: &legacyFollowerReq,
	}, membership.ApplyBoth)
	require.NoError(t, arLegacyFollower.Err)
	require.Equal(t, int64(1), countKey(t, follower.kv, "k2"),
		"Legacy removeNeedlessRangeReqs bypassed RBAC CheckTxnAuth on follower!")

	// PR #18680 follower via apply.Apply (needResult=false): rejects with ErrPermissionDenied!
	followerFixed := newTestNode(t)
	setupAuth(followerFixed)
	arFollowerFixed, _ := apply.Apply(lg, makeEntry(), followerFixed.ua, followerFixed.w, membership.ApplyBoth)
	require.ErrorIs(t, arFollowerFixed.Err, auth.ErrPermissionDenied)
	require.Equal(t, int64(0), countKey(t, followerFixed.kv, "k2"))
}

// TestMainSkipRangeExecution_InvalidSortTargetAsymmetry_FixedByPR18680 demonstrates
// the remaining leader-vs-follower asymmetry in main's SkipRangeExecution
// (!needResult && raftReq.Txn != nil) identified by the Lean proof of executeTxn (GetOk):
// checkRange (range.go:174-184) only checks req.Revision, NOT req.SortTarget.
// When a write Txn contains a RequestRange with an invalid SortTarget (e.g. 99),
// checkTxn succeeds on all nodes; then:
// - With SkipRangeExecution=false (leader on main, or ALL nodes under PR #18680),
//   executeRange -> sortRangeResults panics ("unexpected sort target") before txnWrite.End(),
//   so the write is NOT committed.
// - With SkipRangeExecution=true (followers on main), executeTxn skips executeRange,
//   does NOT panic, and txnWrite.End() commits the write to MVCC and BoltDB!
func TestMainSkipRangeExecution_InvalidSortTargetAsymmetry_FixedByPR18680(t *testing.T) {
	lg := zaptest.NewLogger(t)
	reqID := uint64(99)
	makeRaftReq := func() *pb.InternalRaftRequest {
		return &pb.InternalRaftRequest{
			Header: &pb.RequestHeader{ID: reqID},
			Txn: &pb.TxnRequest{
				Success: []*pb.RequestOp{
					{
						Request: &pb.RequestOp_RequestPut{
							RequestPut: &pb.PutRequest{
								Key:   []byte("k-asym"),
								Value: []byte("written"),
							},
						},
					},
					{
						Request: &pb.RequestOp_RequestRange{
							RequestRange: &pb.RangeRequest{
								Key:        []byte("k-asym"),
								SortTarget: pb.RangeRequest_SortTarget(99), // invalid SortTarget
								SortOrder:  pb.RangeRequest_ASCEND,
							},
						},
					},
				},
			},
		}
	}

	// 1. On main (with SkipRangeExecution = !needResult && raftReq.Txn != nil):
	// Leader (SkipRangeExecution=false) panics in sortRangeResults, while
	// Follower (SkipRangeExecution=true) skips executeRange and commits "k-asym"!
	mainLeader := newTestNodeNoClose(t)
	mainFollower := newTestNode(t)

	require.PanicsWithValue(t, "unexpected sort target", func() {
		mainLeader.ua.Apply(&apply.InternalRaftRequestWrapper{
			InternalRaftRequest: makeRaftReq(),
			SkipRangeExecution:  false, // leader (needResult=true)
		}, membership.ApplyBoth)
	})
	arMainFollower := mainFollower.ua.Apply(&apply.InternalRaftRequestWrapper{
		InternalRaftRequest: makeRaftReq(),
		SkipRangeExecution:  true, // follower on main (needResult=false)
	}, membership.ApplyBoth)
	require.NoError(t, arMainFollower.Err)
	require.Equal(t, int64(1), countKey(t, mainFollower.kv, "k-asym"),
		"On main (SkipRangeExecution=true), follower commits k-asym while leader panics!")

	// 2. Under PR #18680 (apply.Apply always sets SkipRangeExecution=false):
	// Both leader (needResult=true) and follower (needResult=false) behave identically (both panic).
	prLeader := newTestNodeNoClose(t)
	prFollower := newTestNodeNoClose(t)
	_ = prLeader.w.Register(reqID)
	entry := mustMarshalEntry(t, makeRaftReq())

	require.PanicsWithValue(t, "unexpected sort target", func() {
		apply.Apply(lg, entry, prLeader.ua, prLeader.w, membership.ApplyBoth)
	})
	require.PanicsWithValue(t, "unexpected sort target", func() {
		apply.Apply(lg, entry, prFollower.ua, prFollower.w, membership.ApplyBoth)
	})
}

// TestCheckRangeVsRangeKeys_NegativeRevisionAfterCompaction demonstrates the validation
// discrepancy between standalone txn.Range (which uses mvcc.rangeKeys: `if rev <= 0 { rev = curRev }`)
// and txn.Txn's checkRange (range.go:174-184: `case req.Revision == 0: return nil; case req.Revision < rv.FirstRev(): return mvcc.ErrCompacted`).
// After compaction at revision 2 (FirstRev() == 2):
// - Standalone txn.Range with Revision: -1 treats rev <= 0 as curRev and SUCCEEDS.
// - Inside txn.Txn, checkRange checks Revision == 0 (not <= 0), so -1 < FirstRev() (2)
//   fails with mvcc.ErrCompacted!
func TestCheckRangeVsRangeKeys_NegativeRevisionAfterCompaction(t *testing.T) {
	lg := zaptest.NewLogger(t)
	node := newTestNode(t)

	tw := node.kv.Write(traceutil.TODO())
	tw.Put([]byte("k"), []byte("v1"), lease.NoLease)
	tw.End()
	tw = node.kv.Write(traceutil.TODO())
	tw.Put([]byte("k"), []byte("v2"), lease.NoLease)
	tw.End()

	// Before compaction, FirstRev() is -1, so Revision: -1 passes checkRange (-1 < -1 is false)!
	txnReq := &pb.TxnRequest{
		Success: []*pb.RequestOp{
			{
				Request: &pb.RequestOp_RequestRange{
					RequestRange: &pb.RangeRequest{
						Key:      []byte("k"),
						Revision: -1,
					},
				},
			},
		},
	}
	respBefore, _, err := txn.Txn(context.Background(), lg, txnReq, false, node.kv, &lease.FakeLessor{}, false)
	require.NoError(t, err, "before compaction (FirstRev=-1), Revision=-1 passes checkRange")
	require.Len(t, respBefore.Responses[0].GetResponseRange().Kvs, 1)

	// Now compact at revision 2 (FirstRev becomes 2).
	_, err = node.kv.Compact(traceutil.TODO(), 2)
	require.NoError(t, err)

	// Standalone Range with Revision: -1 still succeeds after compaction because rangeKeys checks `if rev <= 0 { rev = curRev }`:
	rangeResp, _, err := txn.Range(context.Background(), lg, node.kv, &pb.RangeRequest{
		Key:      []byte("k"),
		Revision: -1,
	}, true)
	require.NoError(t, err, "standalone Range(Revision=-1) succeeds after compaction")
	require.Len(t, rangeResp.Kvs, 1)

	// Inside Txn, checkRange fails with ErrCompacted for Revision: -1 after compaction!
	_, _, err = txn.Txn(context.Background(), lg, txnReq, false, node.kv, &lease.FakeLessor{}, false)
	require.ErrorIs(t, err, mvcc.ErrCompacted,
		"inside Txn, checkRange rejects Revision=-1 with ErrCompacted once FirstRev > -1")
}
