// Reproduction of issues/etcd-snapshot-applied-index-stale.md (etcd-io/etcd#22528, #22516).
//
// Drop into package etcdserver of go.etcd.io/etcd/server/v3 (directory server/etcdserver of
// upamanyus/etcd at 107edf7e4, the pin of etc/goose.py; also etcd-io/etcd main at ea8b59433),
// next to server_test.go, whose helpers it uses (newNopReadyNode, newNopTransporter,
// uberApplierMock), and run
//
//	cd server && go test ./etcdserver -run TestSnapshotLeavesAppliedIndexStale -count=1
//
// It passes at the pin, showing the bug: after the apply thread applies a leader snapshot at
// index 10001 and no entry follows, s.AppliedIndex() is still 0 while s.CommittedIndex() is
// 10001, so a proposal is refused with ErrTooManyRequests (exceedsRequestLimit's
// committed - applied > 5000) and never reaches raft. Adapted from the test of etcd-io/etcd
// PR #22510 (which asserts the fixed behavior).
package etcdserver

import (
	"context"
	errorspkg "errors"
	"io"
	"os"
	"sync"
	"testing"
	"time"

	"github.com/stretchr/testify/require"
	"go.uber.org/zap/zaptest"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/client/pkg/v3/types"
	"go.etcd.io/etcd/client/pkg/v3/verify"
	"go.etcd.io/etcd/pkg/v3/idutil"
	"go.etcd.io/etcd/pkg/v3/notify"
	"go.etcd.io/etcd/server/v3/auth"
	"go.etcd.io/etcd/server/v3/config"
	"go.etcd.io/etcd/server/v3/etcdserver/api/membership"
	"go.etcd.io/etcd/server/v3/etcdserver/api/snap"
	"go.etcd.io/etcd/server/v3/etcdserver/cindex"
	"go.etcd.io/etcd/server/v3/etcdserver/errors"
	"go.etcd.io/etcd/server/v3/features"
	"go.etcd.io/etcd/server/v3/lease"
	"go.etcd.io/etcd/server/v3/mock/mockstorage"
	serverstorage "go.etcd.io/etcd/server/v3/storage"
	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
	"go.etcd.io/etcd/server/v3/storage/mvcc"
	"go.etcd.io/etcd/server/v3/storage/schema"
	"go.etcd.io/raft/v3"
	"go.etcd.io/raft/v3/raftpb"
)

func TestSnapshotLeavesAppliedIndexStale(t *testing.T) {
	revertFunc := verify.DisableVerifications()
	defer revertFunc()

	lg := zaptest.NewLogger(t)
	n := newNopReadyNode()
	cl := membership.NewCluster(lg)
	be, _ := betesting.NewDefaultTmpBackend(t)
	cl.SetBackend(schema.NewMembershipBackend(lg, be))

	testdir := t.TempDir()
	require.NoError(t, os.MkdirAll(testdir+"/member/snap", 0o755))

	// A leader snapshot far ahead of anything the member has applied (a fresh joiner).
	snapIndex := uint64(2*maxGapBetweenApplyAndCommitIndex + 1)
	snapshotter := snap.New(lg, testdir)
	snapBe, _ := betesting.NewDefaultTmpBackend(t)
	t.Cleanup(func() { betesting.Close(t, snapBe) })
	snapKV := mvcc.New(lg, snapBe, &lease.FakeLessor{}, mvcc.StoreConfig{})
	t.Cleanup(func() { require.NoError(t, snapKV.Close()) })
	auth.NewAuthStore(lg, schema.NewAuthBackend(lg, snapBe), nil, 1)
	snapBe.ForceCommit()
	pr, pw := io.Pipe()
	go func() {
		bs := snapBe.Snapshot()
		_, err := bs.WriteTo(pw)
		pw.CloseWithError(errorspkg.Join(err, bs.Close()))
	}()
	_, err := snapshotter.SaveDBFrom(pr, snapIndex)
	require.NoError(t, err)

	rs := raft.NewMemoryStorage()
	r := newRaftNode(raftNodeConfig{
		lg:          lg,
		isIDRemoved: func(id uint64) bool { return cl.IsIDRemoved(types.ID(id)) },
		Node:        n,
		transport:   newNopTransporter(),
		storage:     mockstorage.NewStorageRecorder(testdir),
		raftStorage: rs,
	})
	ci := cindex.NewConsistentIndex(be)
	s := &EtcdServer{
		lgMu: new(sync.RWMutex),
		lg:   lg,
		Cfg: config.ServerConfig{
			Logger:            lg,
			DataDir:           testdir,
			MaxRequestBytes:   1024 * 1024,
			ServerFeatureGate: features.NewDefaultServerFeatureGate("test", lg),
		},
		r:                 *r,
		snapshotter:       snapshotter,
		cluster:           cl,
		consistIndex:      ci,
		beHooks:           serverstorage.NewBackendHooks(lg, ci),
		firstCommitInTerm: notify.NewNotifier(),
		lessor:            &lease.FakeLessor{},
		uberApply:         uberApplierMock{},
		authStore:         auth.NewAuthStore(lg, schema.NewAuthBackend(lg, be), nil, 1),
		reqIDGen:          idutil.NewGenerator(0, time.Time{}),
	}
	s.kv = mvcc.New(lg, be, &lease.FakeLessor{}, mvcc.StoreConfig{})
	s.be = be

	s.start()
	defer s.Stop()

	idx, term := snapIndex, uint64(1)
	n.readyc <- raft.Ready{Snapshot: &raftpb.Snapshot{Metadata: &raftpb.SnapshotMetadata{
		Index:     &idx,
		Term:      &term,
		ConfState: &raftpb.ConfState{Voters: []uint64{1}},
	}}}
	select {
	case <-s.ApplyWait(snapIndex): // applyAll triggers applyWait at ep.appliedi = snapIndex
	case <-time.After(10 * time.Second):
		t.Fatal("timed out waiting for the snapshot to be applied")
	}

	// The bug: the snapshot is applied (applyWait fired at its index, ep.appliedi = snapIndex),
	// the committed index is the snapshot's, but the server's applied index is still 0.
	require.Equal(t, snapIndex, s.CommittedIndex())
	require.Equal(t, uint64(0), s.AppliedIndex())

	// So every proposal is refused before reaching raft, until some entry is applied.
	ctx, cancel := context.WithTimeout(context.Background(), 100*time.Millisecond)
	defer cancel()
	_, err = s.Put(ctx, &pb.PutRequest{Key: []byte("foo"), Value: []byte("bar")})
	require.ErrorIs(t, err, errors.ErrTooManyRequests)
	for _, a := range n.Action() {
		require.NotEqual(t, "Propose", a.Name)
	}
}
