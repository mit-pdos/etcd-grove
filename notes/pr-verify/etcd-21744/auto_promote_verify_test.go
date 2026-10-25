package etcdserver

import (
	"context"
	errorspkg "errors"
	"sync"
	"testing"
	"time"

	ptestutil "github.com/prometheus/client_golang/prometheus/testutil"
	"github.com/stretchr/testify/require"
	"go.uber.org/zap"
	"go.uber.org/zap/zapcore"
	"go.uber.org/zap/zaptest"
	"go.uber.org/zap/zaptest/observer"

	"go.etcd.io/etcd/client/pkg/v3/types"
	"go.etcd.io/etcd/pkg/v3/idutil"
	"go.etcd.io/etcd/pkg/v3/notify"
	"go.etcd.io/etcd/pkg/v3/pbutil"
	"go.etcd.io/etcd/pkg/v3/wait"
	"go.etcd.io/etcd/server/v3/auth"
	"go.etcd.io/etcd/server/v3/config"
	"go.etcd.io/etcd/server/v3/etcdserver/api/membership"
	"go.etcd.io/etcd/server/v3/etcdserver/cindex"
	"go.etcd.io/etcd/server/v3/etcdserver/errors"
	"go.etcd.io/etcd/server/v3/mock/mockstorage"
	"go.etcd.io/etcd/server/v3/storage/backend/testing"
	"go.etcd.io/etcd/server/v3/storage/schema"
	"go.etcd.io/raft/v3"
	"go.etcd.io/raft/v3/raftpb"
	"go.etcd.io/raft/v3/tracker"
)

type autoPromoteStubNode struct {
	nodeRecorder
	status            raft.Status
	proposeConfChange func(ctx context.Context, conf raftpb.ConfChangeI) error
}

func (n *autoPromoteStubNode) Status() raft.Status {
	return n.status
}

func (n *autoPromoteStubNode) ProposeConfChange(ctx context.Context, conf raftpb.ConfChangeI) error {
	if n.proposeConfChange != nil {
		return n.proposeConfChange(ctx, conf)
	}
	return nil
}

func newAutoPromoteTestServer(t *testing.T, lg *zap.Logger, node raft.Node) (*EtcdServer, context.CancelFunc) {
	t.Helper()
	be, _ := betesting.NewDefaultTmpBackend(t)
	t.Cleanup(func() {
		betesting.Close(t, be)
	})
	schema.CreateMetaBucket(be.BatchTx())

	cl := membership.NewCluster(lg)
	cl.SetBackend(schema.NewMembershipBackend(lg, be))
	cl.AddMember(&membership.Member{
		ID:             types.ID(1),
		RaftAttributes: membership.RaftAttributes{PeerURLs: []string{"http://127.0.0.1:2380"}, IsLearner: false},
		Attributes:     membership.Attributes{Name: "leader1", ClientURLs: []string{"http://127.0.0.1:2379"}},
	}, true)
	cl.AddMember(&membership.Member{
		ID:             types.ID(2),
		RaftAttributes: membership.RaftAttributes{PeerURLs: []string{"http://127.0.0.1:22380"}, IsLearner: true},
		Attributes:     membership.Attributes{Name: "learner2", ClientURLs: []string{"http://127.0.0.1:22379"}},
	}, true)

	ctx, cancel := context.WithCancel(context.Background())
	s := &EtcdServer{
		Cfg: config.ServerConfig{
			TickMs:        1,
			ElectionTicks: 5,
		},
		lgMu:         new(sync.RWMutex),
		lg:           lg,
		memberID:     types.ID(1),
		r:            *newRaftNode(raftNodeConfig{lg: lg, Node: node, storage: mockstorage.NewStorageRecorder(""), transport: newNopTransporter()}),
		cluster:      cl,
		w:            wait.New(),
		reqIDGen:     idutil.NewGenerator(1, time.Unix(0, 0)),
		stopping:          make(chan struct{}),
		done:              make(chan struct{}),
		applyWait:         wait.NewTimeList(),
		firstCommitInTerm: notify.NewNotifier(),
		consistIndex:      cindex.NewFakeConsistentIndex(10),
		authStore:    auth.NewAuthStore(lg, schema.NewAuthBackend(lg, be), nil, 0),
		be:           be,
		ctx:          ctx,
		cancel:       cancel,
	}
	s.appliedIndex.Store(10)
	s.committedIndex.Store(10)
	s.applyWait.Trigger(10)
	return s, cancel
}

func readyLeaderStatus() raft.Status {
	st := raft.Status{
		BasicStatus: raft.BasicStatus{
			ID:             1,
			SoftState:      raft.SoftState{Lead: 1, RaftState: raft.StateLeader},
			Applied:        10,
		},
		Progress: map[uint64]tracker.Progress{
			1: {Match: 10, Next: 11},
			2: {Match: 10, Next: 11, IsLearner: true},
		},
	}
	return st
}

// TestVerifyPR21744_Finding1_MissingReqTimeoutDeadlocksMonitor reproduces Finding 1:
//
//  1. In go.etcd.io/raft/v3 (stepLeader, raft.go:1326-1353), if a ConfChange is proposed
//     while an earlier ConfChange is still pending (r.pendingConfIndex > r.raftLog.applied),
//     ProposeConfChange returns nil (no error!) and rewrites the second EntryConfChange
//     in-place into an empty pb.EntryNormal{Type: EntryNormal, Data: nil}. When EtcdServer
//     applies that entry in applyEntryNormal (server.go:1980), len(e.Data) == 0 returns
//     early without calling s.w.Trigger(cc.GetId(), ...).
//  2. In tryAutoPromoteLearners (server.go:2400), ctx := s.authStore.WithRoot(s.ctx) has
//     no deadline, and s.promoteMember(ctx, id) -> s.configure(ctx, &cc) does not wrap ctx
//     with context.WithTimeout(ctx, s.Cfg.ReqTimeout()).
//  3. Consequently, tryAutoPromoteLearners blocks forever on <-ch inside s.configure,
//     permanently wedging monitorAutoPromoteLearners and leaking s.w.Register(cc.GetId()).
//     Moreover, errors.ErrTimeout in tryAutoPromoteLearners's switch is dead code.
func TestVerifyPR21744_Finding1_MissingReqTimeoutDeadlocksMonitor(t *testing.T) {
	lg := zaptest.NewLogger(t)

	// Part A: Demonstrate on a real go.etcd.io/raft/v3 RawNode that a second ConfChange
	// proposed while pendingConfIndex > applied returns err == nil from ProposeConfChange
	// and is rewritten in-place into an empty EntryNormal (len(Data) == 0).
	storage := raft.NewMemoryStorage()
	rn, err := raft.NewRawNode(&raft.Config{
		ID:              1,
		ElectionTick:    10,
		HeartbeatTick:   1,
		Storage:         storage,
		MaxSizePerMsg:   1024 * 1024,
		MaxInflightMsgs: 256,
	})
	require.NoError(t, err)
	require.NoError(t, rn.Bootstrap([]raft.Peer{{ID: 1}}))
	// Drain bootstrap Ready and apply the bootstrap ConfChange so node 1 can campaign.
	rd := rn.Ready()
	if !raft.IsEmptyHardState(rd.HardState) {
		require.NoError(t, storage.SetHardState(rd.HardState))
	}
	if len(rd.Entries) > 0 {
		require.NoError(t, storage.Append(rd.Entries))
	}
	for _, ent := range rd.CommittedEntries {
		if ent.GetType() == raftpb.EntryConfChange {
			var cc raftpb.ConfChange
			pbutil.MustUnmarshalMessage(&cc, ent.GetData())
			rn.ApplyConfChange(&cc)
		}
	}
	rn.Advance(rd)

	require.NoError(t, rn.Campaign())
	// Drain campaign Ready to establish leadership at term 1.
	rd = rn.Ready()
	if !raft.IsEmptyHardState(rd.HardState) {
		require.NoError(t, storage.SetHardState(rd.HardState))
	}
	if len(rd.Entries) > 0 {
		require.NoError(t, storage.Append(rd.Entries))
	}
	rn.Advance(rd)

	// Propose first ConfChange (sets pendingConfIndex > applied because we haven't applied it yet).
	cc1 := &raftpb.ConfChange{Id: new(uint64(101)), Type: raftpb.ConfChangeAddLearnerNode.Enum(), NodeId: new(uint64(2))}
	require.NoError(t, rn.ProposeConfChange(cc1))

	// Propose second ConfChange (the learner promotion with ID 102) while cc1 is still unapplied.
	cc2 := &raftpb.ConfChange{Id: new(uint64(102)), Type: raftpb.ConfChangeAddNode.Enum(), NodeId: new(uint64(2)), Context: []byte(`{"IsPromote":true}`)}
	err = rn.ProposeConfChange(cc2)
	require.NoError(t, err, "raft.ProposeConfChange returns nil even when pendingConfIndex > applied")

	rd2 := rn.Ready()
	require.GreaterOrEqual(t, len(rd2.Entries), 2)
	firstCCEnt := rd2.Entries[len(rd2.Entries)-2]
	rewrittenEnt := rd2.Entries[len(rd2.Entries)-1]
	require.Equal(t, raftpb.EntryConfChange, firstCCEnt.GetType())
	// The second ConfChange (cc2) was silently rewritten into an empty EntryNormal!
	require.Equal(t, raftpb.EntryNormal, rewrittenEnt.GetType(), "second ConfChange rewritten to EntryNormal")
	require.Empty(t, rewrittenEnt.GetData(), "rewritten EntryNormal has empty Data, so applyEntryNormal will not trigger s.w")
	t.Logf("Part A confirmed: raft.ProposeConfChange returned nil and rewrote second ConfChange (ID=%d) to %v at Index=%d with len(Data)=%d",
		cc2.GetId(), rewrittenEnt.GetType(), rewrittenEnt.GetIndex(), len(rewrittenEnt.GetData()))

	// Part B: Show that s.tryAutoPromoteLearners() passes a deadline-free ctx to s.configure,
	// so when the proposed ConfChange is rewritten to an empty EntryNormal (or dropped before commit),
	// tryAutoPromoteLearners blocks past ReqTimeout() and leaks the wait registration in s.w.
	proposeEntered := make(chan uint64, 1)
	stub := &autoPromoteStubNode{
		status: readyLeaderStatus(),
	}
	s, cancel := newAutoPromoteTestServer(t, lg, stub)
	defer cancel()

	stub.proposeConfChange = func(ctx context.Context, conf raftpb.ConfChangeI) error {
		_, hasDeadline := ctx.Deadline()
		require.False(t, hasDeadline, "Finding 1: ctx passed from tryAutoPromoteLearners to ProposeConfChange has NO deadline")
		ccV1, ok := conf.AsV1()
		require.True(t, ok)
		// Apply the rewritten empty EntryNormal exactly as EtcdServer.applyEntries does:
		// applyEntryNormal returns early on len(e.Data) == 0 without calling s.w.Trigger(cc.GetId(), ...).
		s.applyEntryNormal(rewrittenEnt, membership.ApplyBoth)
		proposeEntered <- ccV1.GetId()
		return nil
	}

	doneCh := make(chan struct{})
	go func() {
		defer close(doneCh)
		s.tryAutoPromoteLearners()
	}()

	var ccID uint64
	select {
	case ccID = <-proposeEntered:
	case <-time.After(2 * time.Second):
		t.Fatal("timed out waiting for tryAutoPromoteLearners to call ProposeConfChange")
	}

	reqTimeout := s.Cfg.ReqTimeout()
	t.Logf("Server ReqTimeout() = %v; waiting %v to verify tryAutoPromoteLearners is permanently blocked in s.configure",
		reqTimeout, reqTimeout+250*time.Millisecond)

	select {
	case <-doneCh:
		t.Fatal("unexpected: tryAutoPromoteLearners returned despite no deadline on ctx")
	case <-time.After(reqTimeout + 250*time.Millisecond):
		// Still blocked past ReqTimeout()!
	}

	require.True(t, s.w.IsRegistered(ccID), "Finding 1: wait registration cc.Id=%d is leaked in s.w while configure is blocked", ccID)
	t.Logf("Part B confirmed: tryAutoPromoteLearners remained blocked past ReqTimeout (%v) and s.w.IsRegistered(%d)=true",
		reqTimeout, ccID)

	// Part C: Even when s.ctx is canceled on server shutdown, parseProposeCtxErr returns
	// errors.ErrCanceled, never errors.ErrTimeout (confirming errors.ErrTimeout in the switch is dead code).
	parsedOnCancel := s.parseProposeCtxErr(context.Canceled, time.Now())
	require.ErrorIs(t, parsedOnCancel, errors.ErrCanceled)
	require.False(t, errorspkg.Is(parsedOnCancel, errors.ErrTimeout),
		"Finding 1: canceling s.ctx produces ErrCanceled, never ErrTimeout")

	// Unblock the wedged goroutine by canceling s.ctx and verify it exits via ctx.Done().
	cancel()
	select {
	case <-doneCh:
	case <-time.After(2 * time.Second):
		t.Fatal("tryAutoPromoteLearners did not exit after s.ctx was canceled")
	}
	require.False(t, s.w.IsRegistered(ccID), "s.w registration cleaned up only after server-wide s.ctx cancellation")

	// Part D: Verify the fix: wrapping ctx with context.WithTimeout(ctx, timeout) unblocks
	// promoteMember with errors.ErrTimeout and cleans up s.w.
	s2, cancel2 := newAutoPromoteTestServer(t, lg, &autoPromoteStubNode{
		status: readyLeaderStatus(),
		proposeConfChange: func(ctx context.Context, conf raftpb.ConfChangeI) error {
			_, hasDeadline := ctx.Deadline()
			require.True(t, hasDeadline, "Fixed caller passes a ctx with a deadline")
			return nil
		},
	})
	defer cancel2()

	fixedCtx, fixedCancel := context.WithTimeout(s2.authStore.WithRoot(s2.ctx), 50*time.Millisecond)
	defer fixedCancel()
	_, err = s2.promoteMember(fixedCtx, 2)
	require.ErrorIs(t, err, errors.ErrTimeout, "With a per-attempt deadline, promoteMember returns errors.ErrTimeout")
	t.Logf("Part D confirmed: wrapping ctx with context.WithTimeout causes promoteMember to return %v and clean up s.w", err)
}

// TestVerifyPR21744_Finding2_TransientErrorsCountedAsFailed reproduces Finding 2:
//
// When s.promoteMember returns transient leadership-flip / proposal-timeout errors
// that can arise from ProposeConfChange or parseProposeCtxErr:
//   - raft.ErrProposalDropped
//   - errors.ErrTimeoutDueToLeaderFail
//   - errors.ErrTimeoutDueToConnectionLost
// tryAutoPromoteLearners's 10-way switch misses all 10 cases and falls through to
// default:, incrementing learnerPromoteFailed and logging Warn("auto-promote failed").
func TestVerifyPR21744_Finding2_TransientErrorsCountedAsFailed(t *testing.T) {
	transientErrs := []error{
		raft.ErrProposalDropped,
		errors.ErrTimeoutDueToLeaderFail,
		errors.ErrTimeoutDueToConnectionLost,
	}

	for _, transientErr := range transientErrs {
		t.Run(transientErr.Error(), func(t *testing.T) {
			core, recorded := observer.New(zapcore.DebugLevel)
			lg := zap.New(core)

			stub := &autoPromoteStubNode{
				status: readyLeaderStatus(),
				proposeConfChange: func(ctx context.Context, conf raftpb.ConfChangeI) error {
					return transientErr
				},
			}
			s, cancel := newAutoPromoteTestServer(t, lg, stub)
			defer cancel()

			counter := learnerPromoteFailed.WithLabelValues(transientErr.Error())
			before := ptestutil.ToFloat64(counter)

			s.tryAutoPromoteLearners()

			after := ptestutil.ToFloat64(counter)
			require.Equal(t, before+1, after,
				"Finding 2: transient error %q incremented learnerPromoteFailed in default branch", transientErr)

			warnLogs := recorded.FilterMessage("auto-promote failed").All()
			skipLogs := recorded.FilterMessage("auto-promote skipped").All()
			require.Len(t, warnLogs, 1, "Finding 2: transient error %q logged WARN 'auto-promote failed'", transientErr)
			require.Equal(t, zapcore.WarnLevel, warnLogs[0].Level)
			require.Empty(t, skipLogs, "Finding 2: transient error %q was not classified as 'auto-promote skipped'", transientErr)

			t.Logf("Confirmed: transient error %q -> learnerPromoteFailed=%v->%v, logged %s %q",
				transientErr.Error(), before, after, warnLogs[0].Level, warnLogs[0].Message)
		})
	}
}
