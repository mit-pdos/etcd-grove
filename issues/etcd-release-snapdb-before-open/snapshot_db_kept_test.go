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

import (
	"bytes"
	"fmt"
	"os"
	"path/filepath"
	"sync"
	"testing"
	"time"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
	"go.uber.org/zap/zaptest"

	"go.etcd.io/etcd/client/pkg/v3/fileutil"
	"go.etcd.io/etcd/client/pkg/v3/types"
	"go.etcd.io/etcd/client/pkg/v3/verify"
	"go.etcd.io/etcd/server/v3/config"
	"go.etcd.io/etcd/server/v3/etcdserver/api/membership"
	"go.etcd.io/etcd/server/v3/etcdserver/api/snap"
	"go.etcd.io/etcd/server/v3/etcdserver/api/v3alarm"
	"go.etcd.io/etcd/server/v3/etcdserver/cindex"
	"go.etcd.io/etcd/server/v3/features"
	"go.etcd.io/etcd/server/v3/lease"
	serverstorage "go.etcd.io/etcd/server/v3/storage"
	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
	"go.etcd.io/etcd/server/v3/storage/mvcc"
	"go.etcd.io/etcd/server/v3/storage/schema"
	"go.etcd.io/etcd/server/v3/storage/wal"
	"go.etcd.io/raft/v3"
	"go.etcd.io/raft/v3/raftpb"
)

// TestSnapshotDBKeptUntilOpened ensures that a snapshot's .snap.db file stays
// until applySnapshot has opened it, when raft hands out a second snapshot
// before the apply loop has reached the first one's file.
func TestSnapshotDBKeptUntilOpened(t *testing.T) {
	// Ignore the snapshot index verification in unit test, because
	// it doesn't follow the e2e applying logic.
	revertFunc := verify.DisableVerifications()
	defer revertFunc()

	lg := zaptest.NewLogger(t)
	n := newNopReadyNode()
	cl := membership.NewCluster(lg)
	be, bePath := betesting.NewDefaultTmpBackend(t)
	cl.SetBackend(schema.NewMembershipBackend(lg, be))

	testdir := t.TempDir()
	snapdir := filepath.Join(testdir, "member", "snap")
	require.NoError(t, os.MkdirAll(snapdir, 0o755))
	w, err := wal.Create(lg, filepath.Join(testdir, "member", "wal"), nil)
	require.NoError(t, err)
	ss := snap.New(lg, snapdir)

	rs := raft.NewMemoryStorage()
	r := newRaftNode(raftNodeConfig{
		lg:          lg,
		isIDRemoved: func(id uint64) bool { return cl.IsIDRemoved(types.ID(id)) },
		Node:        n,
		transport:   newNopTransporter(),
		storage:     serverstorage.NewStorage(lg, w, ss),
		raftStorage: rs,
	})
	ci := cindex.NewConsistentIndex(be)
	cfg := config.ServerConfig{
		Logger:                 lg,
		DataDir:                testdir,
		SnapshotCatchUpEntries: DefaultSnapshotCatchUpEntries,
		ServerFeatureGate:      features.NewDefaultServerFeatureGate("test", lg),
	}
	alarmStore, err := v3alarm.NewAlarmStore(lg, schema.NewAlarmBackend(lg, be))
	require.NoError(t, err)

	s := &EtcdServer{
		lgMu:         new(sync.RWMutex),
		lg:           lg,
		Cfg:          cfg,
		r:            *r,
		snapshotter:  ss,
		cluster:      cl,
		consistIndex: ci,
		beHooks:      serverstorage.NewBackendHooks(lg, ci),
		alarmStore:   alarmStore,
	}
	s.kv = mvcc.New(lg, be, &lease.FakeLessor{}, mvcc.StoreConfig{})
	s.be = be
	be.ForceCommit()
	db, err := os.ReadFile(bePath)
	require.NoError(t, err)

	// the .snap.db files of two snapshots, as rafthttp saves them on receipt
	snapshot := func(index uint64) *raftpb.Snapshot {
		_, err := ss.SaveDBFrom(bytes.NewReader(db), index)
		require.NoError(t, err)
		return &raftpb.Snapshot{Metadata: &raftpb.SnapshotMetadata{
			Index:     new(index),
			Term:      new(uint64(1)),
			ConfState: &raftpb.ConfState{Voters: []uint64{1}},
		}}
	}
	snap1, snap2 := snapshot(2), snapshot(4)
	snap1Path := filepath.Join(snapdir, fmt.Sprintf("%016x.snap.db", 2))

	s.start()
	defer s.Stop()

	// hold applySnapshot of the first snapshot before it opens the snapshot's
	// backend (it takes bemu first)
	s.bemu.RLock()
	bemuHeld := true
	defer func() {
		if bemuHeld {
			s.bemu.RUnlock()
		}
	}()

	n.readyc <- raft.Ready{Snapshot: snap1}
	// raft hands out a newer snapshot once the apply loop has taken the first
	// one's "persisted" signal
	n.readyc <- raft.Ready{Snapshot: snap2, Entries: []*raftpb.Entry{{Index: new(uint64(5)), Term: new(uint64(1))}}}

	// wait for raftNode to process the second snapshot, up to the append of
	// its entries to the raft log
	deadline := time.Now().Add(10 * time.Second)
	for {
		last, err := rs.LastIndex()
		require.NoError(t, err)
		if last == 5 {
			break
		}
		if time.Now().After(deadline) {
			t.Fatalf("raftNode did not process the second snapshot")
		}
		time.Sleep(time.Millisecond)
	}

	if !fileutil.Exist(snap1Path) {
		t.Errorf("expected file %q, got missing: released before applySnapshot opened it", snap1Path)
		// put it back so that applySnapshot can proceed
		_, err := ss.SaveDBFrom(bytes.NewReader(db), 2)
		require.NoError(t, err)
	}

	s.bemu.RUnlock()
	bemuHeld = false

	select {
	case <-s.applyWait.Wait(4):
	case <-time.After(time.Until(deadline)):
		t.Fatalf("the apply loop did not apply the second snapshot")
	}
	snapDBs, err := filepath.Glob(filepath.Join(snapdir, "*.snap.db"))
	require.NoError(t, err)
	assert.Empty(t, snapDBs, "both snapshots' .snap.db files are opened and released")
}
