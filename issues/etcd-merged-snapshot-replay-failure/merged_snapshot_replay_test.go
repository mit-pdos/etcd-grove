// Copyright 2026 The etcd Authors
// SPDX-License-Identifier: Apache-2.0

package etcdserver

import (
	"io"
	"os"
	"path/filepath"
	"sync"
	"testing"

	"github.com/stretchr/testify/require"
	"go.uber.org/zap/zaptest"
	"google.golang.org/protobuf/proto"

	"go.etcd.io/etcd/pkg/v3/wait"
	"go.etcd.io/etcd/server/v3/config"
	"go.etcd.io/etcd/server/v3/etcdserver/api/snap"
	"go.etcd.io/etcd/server/v3/etcdserver/cindex"
	"go.etcd.io/etcd/server/v3/lease"
	"go.etcd.io/etcd/server/v3/storage/backend"
	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
	"go.etcd.io/etcd/server/v3/storage/mvcc"
	"go.etcd.io/etcd/server/v3/storage/schema"
	"go.etcd.io/raft/v3/raftpb"
)

type replaySnapTransport struct {
	nopTransporter
	send func(*snap.Message)
}

func (tr replaySnapTransport) SendSnapshot(m *snap.Message) { tr.send(m) }

// The member restarts with an applied backend at 7. Its apply loop has
// replayed only through 3 when it takes a current-term MsgSnap. Compare the
// label with the metadata in the database bytes delivered to the follower.
func TestMergedSnapshotDuringReplay(t *testing.T) {
	lg := zaptest.NewLogger(t)
	be, path := betesting.NewDefaultTmpBackend(t)
	conf := &raftpb.ConfState{Voters: []uint64{1, 2, 3}, Learners: []uint64{4}}
	tx := be.BatchTx()
	tx.LockOutsideApply()
	schema.UnsafeCreateMetaBucket(tx)
	schema.UnsafeUpdateConsistentIndex(tx, 7, 2)
	schema.MustUnsafeSaveConfStateToBackend(lg, tx, conf)
	tx.Unlock()
	require.NoError(t, be.Close())

	be = backend.NewDefaultBackend(lg, path)
	defer be.Close()
	ci := cindex.NewConsistentIndex(be)
	require.Equal(t, uint64(7), ci.ConsistentIndex())
	sent := false
	tr := replaySnapTransport{send: func(m *snap.Message) {
		sent = true
		file := filepath.Join(t.TempDir(), "received.db")
		f, err := os.Create(file)
		require.NoError(t, err)
		_, err = io.Copy(f, m.ReadCloser)
		require.NoError(t, err)
		require.NoError(t, f.Close())
		m.CloseWithError(nil)
		received := backend.NewDefaultBackend(lg, file)
		defer received.Close()
		r := received.ReadTx()
		r.RLock()
		i, term := schema.UnsafeReadConsistentIndex(r)
		cs := schema.UnsafeConfStateFromBackend(lg, r)
		r.RUnlock()
		md := m.GetSnapshot().GetMetadata()
		require.Equal(t, uint64(7), i)
		require.Equal(t, uint64(2), term)
		require.True(t, proto.Equal(conf, cs))
		require.Equal(t, i, md.GetIndex())
		require.Equal(t, term, md.GetTerm())
		require.True(t, proto.Equal(cs, md.GetConfState()))
	}}
	r := newRaftNode(raftNodeConfig{lg: lg, Node: newNopReadyNode(), transport: &tr})
	s := &EtcdServer{
		lgMu: new(sync.RWMutex), lg: lg, be: be, consistIndex: ci,
		r: *r, Cfg: config.ServerConfig{SnapshotCount: 1000},
		applyWait: wait.NewTimeList(), stopping: make(chan struct{}),
	}
	s.kv = mvcc.New(lg, be, &lease.FakeLessor{}, mvcc.StoreConfig{})
	defer s.kv.Close()
	defer func() { close(s.stopping); s.wg.Wait() }()
	done := make(chan struct{})
	close(done)
	s.r.msgSnapC <- &raftpb.Message{
		Type: raftpb.MsgSnap.Enum(), From: new(uint64(1)), To: new(uint64(2)), Term: new(uint64(3)),
		Snapshot: &raftpb.Snapshot{Metadata: &raftpb.SnapshotMetadata{Index: new(uint64(3)), Term: new(uint64(1))}},
	}
	ep := etcdProgress{appliedi: 3, appliedt: 1, confState: &raftpb.ConfState{Voters: []uint64{1, 2, 3}}}
	s.applyAll(&ep, &toApply{notifyc: done, raftAdvancedC: done, raftTerm: 3})
	require.True(t, sent, "applyAll did not deliver the current-term snapshot")
}
