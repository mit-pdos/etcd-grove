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

package etcdserver

// Reproduction of issues/etcd-merged-snapshot-stale-term.md, etcd side:
// the real raftNode loop and applyAll, fed two Readys by a fake raft node,
// merge a MsgSnap queued in the first Ready with the content applied from
// the second, keeping the message's older term.
//
// Ready 1 (member 1 a follower, as after stepping down at term 2): the
// committed entry (1, term 1) and two MsgSnaps of term 1 that it made while
// leader, to 5 and to 4. processMessages pushes them onto msgSnapC (4's
// first); job 1 merges 4's.
// Ready 2: HardState term 2, the committed entry (2, term 2). Job 2 applies
// it and merges 5's: Term 1, Snapshot (2, term 2).

import (
	"os"
	"path/filepath"
	"sync"
	"testing"
	"time"

	"github.com/stretchr/testify/require"
	"go.uber.org/zap/zaptest"

	"go.etcd.io/etcd/client/pkg/v3/types"
	"go.etcd.io/etcd/client/pkg/v3/verify"
	"go.etcd.io/etcd/pkg/v3/notify"
	"go.etcd.io/etcd/server/v3/config"
	"go.etcd.io/etcd/server/v3/etcdserver/api/membership"
	"go.etcd.io/etcd/server/v3/etcdserver/api/rafthttp"
	"go.etcd.io/etcd/server/v3/etcdserver/api/snap"
	"go.etcd.io/etcd/server/v3/etcdserver/cindex"
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

type recordSnapTransporter struct {
	nopTransporter
	mu   sync.Mutex
	sent []*raftpb.Message
	c    chan struct{}
}

func (s *recordSnapTransporter) SendSnapshot(m *snap.Message) {
	m.ReadCloser.Close()
	m.CloseWithError(nil)
	s.mu.Lock()
	s.sent = append(s.sent, m.Message)
	s.mu.Unlock()
	s.c <- struct{}{}
}

var _ rafthttp.Transporter = (*recordSnapTransporter)(nil)

func TestMergedSnapshotKeepsStaleTerm(t *testing.T) {
	revertFunc := verify.DisableVerifications()
	defer revertFunc()

	lg := zaptest.NewLogger(t)
	n := newNopReadyNode()
	cl := membership.NewCluster(lg)
	be, _ := betesting.NewDefaultTmpBackend(t)
	cl.SetBackend(schema.NewMembershipBackend(lg, be))

	testdir := t.TempDir()
	snapdir := filepath.Join(testdir, "member", "snap")
	require.NoError(t, os.MkdirAll(snapdir, 0o755))

	rs := raft.NewMemoryStorage()
	tr := &recordSnapTransporter{c: make(chan struct{}, 4)}
	r := newRaftNode(raftNodeConfig{
		lg:          lg,
		isIDRemoved: func(id uint64) bool { return cl.IsIDRemoved(types.ID(id)) },
		Node:        n,
		transport:   tr,
		storage:     mockstorage.NewStorageRecorder(testdir),
		raftStorage: rs,
	})
	ci := cindex.NewConsistentIndex(be)
	s := &EtcdServer{
		lgMu: new(sync.RWMutex),
		lg:   lg,
		Cfg: config.ServerConfig{
			Logger:                 lg,
			DataDir:                testdir,
			SnapshotCatchUpEntries: DefaultSnapshotCatchUpEntries,
			ServerFeatureGate:      features.NewDefaultServerFeatureGate("test", lg),
		},
		r:                 *r,
		snapshotter:       snap.New(lg, snapdir),
		cluster:           cl,
		consistIndex:      ci,
		beHooks:           serverstorage.NewBackendHooks(lg, ci),
		lessor:            &lease.FakeLessor{},
		firstCommitInTerm: notify.NewNotifier(),
	}
	s.kv = mvcc.New(lg, be, &lease.FakeLessor{}, mvcc.StoreConfig{})
	s.be = be
	s.start()
	defer s.Stop()

	snapTo := func(to uint64) *raftpb.Message {
		return &raftpb.Message{
			Type: raftpb.MsgSnap.Enum(), From: new(uint64(1)), To: new(to), Term: new(uint64(1)),
			Snapshot: &raftpb.Snapshot{Metadata: &raftpb.SnapshotMetadata{Index: new(uint64(1)), Term: new(uint64(1))}},
		}
	}
	ent := func(i, term uint64) *raftpb.Entry {
		return &raftpb.Entry{Index: new(i), Term: new(term), Type: raftpb.EntryNormal.Enum()}
	}

	n.readyc <- raft.Ready{
		SoftState:        &raft.SoftState{Lead: 2, RaftState: raft.StateFollower},
		HardState:        &raftpb.HardState{Term: new(uint64(2)), Commit: new(uint64(1))},
		CommittedEntries: []*raftpb.Entry{ent(1, 1)},
		Messages:         []*raftpb.Message{snapTo(5), snapTo(4)},
	}
	waitSent := func() {
		select {
		case <-tr.c:
		case <-time.After(10 * time.Second):
			t.Fatal("no merged snapshot sent")
		}
	}
	waitSent()
	n.readyc <- raft.Ready{
		HardState:        &raftpb.HardState{Term: new(uint64(2)), Commit: new(uint64(2))},
		CommittedEntries: []*raftpb.Entry{ent(2, 2)},
	}
	waitSent()

	tr.mu.Lock()
	defer tr.mu.Unlock()
	require.Len(t, tr.sent, 2)
	first, second := tr.sent[0], tr.sent[1]
	require.Equal(t, uint64(4), first.GetTo())
	require.Equal(t, uint64(1), first.GetSnapshot().GetMetadata().GetTerm())
	// The second merged message: term 1, from 1, content of term 2.
	require.Equal(t, uint64(5), second.GetTo())
	require.Equal(t, uint64(1), second.GetFrom())
	require.Equal(t, uint64(1), second.GetTerm())
	require.Equal(t, uint64(2), second.GetSnapshot().GetMetadata().GetIndex())
	require.Equal(t, uint64(2), second.GetSnapshot().GetMetadata().GetTerm())
	t.Logf("merged MsgSnap to %d: Term=%d, Snapshot (index %d, term %d)", second.GetTo(), second.GetTerm(),
		second.GetSnapshot().GetMetadata().GetIndex(), second.GetSnapshot().GetMetadata().GetTerm())
}
