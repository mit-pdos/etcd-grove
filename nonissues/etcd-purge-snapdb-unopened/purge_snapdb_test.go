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
	"os/exec"
	"path/filepath"
	"strings"
	"sync"
	"testing"
	"time"

	"github.com/stretchr/testify/require"
	"go.uber.org/zap"
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

func snapMeta(index uint64) *raftpb.Snapshot {
	return &raftpb.Snapshot{Metadata: &raftpb.SnapshotMetadata{
		Index:     new(index),
		Term:      new(uint64(1)),
		ConfState: &raftpb.ConfState{Voters: []uint64{1}},
	}}
}

// TestPurgeFileRemovesUnopenedSnapDB: purgeFile, one pass, removes the oldest
// of six .snap.db files whatever their state, so that opening that snapshot
// (OpenSnapshotBackend, which applySnapshot calls, panicking on its error)
// fails.
func TestPurgeFileRemovesUnopenedSnapDB(t *testing.T) {
	lg := zaptest.NewLogger(t)
	testdir := t.TempDir()
	snapdir := filepath.Join(testdir, "member", "snap")
	require.NoError(t, os.MkdirAll(snapdir, 0o755))
	ss := snap.New(lg, snapdir)
	cfg := config.ServerConfig{Logger: lg, DataDir: testdir}

	for _, i := range []uint64{2, 4, 6, 8, 10, 12} {
		_, err := ss.SaveDBFrom(bytes.NewReader([]byte("db")), i)
		require.NoError(t, err)
	}
	stopping := make(chan struct{})
	close(stopping) // one pass, then purgeFile returns
	s := &EtcdServer{lgMu: new(sync.RWMutex), lg: lg, Cfg: cfg, stopping: stopping}
	s.purgeFile()

	// OpenSnapshotBackend's first step
	if _, err := ss.DBFilePath(2); err != nil {
		t.Errorf("snapshot 2's database file was purged before it was opened: %v", err)
	}
}

// TestPurgeSnapDBBeforeApply drives raftNode and the apply loop as
// TestSnapshotDBKeptUntilOpened does: six snapshots' .snap.db files are on
// disk (as rafthttp saves them on receipt), raft hands out the oldest, and the
// apply loop is held before it opens it (bemu, as a slow apply would). The
// purge goroutine Start attaches runs one pass meanwhile. The apply loop must
// then open the snapshot; at the pin it panics ("failed to open snapshot
// backend"). The scenario runs in a child process, since the panic is on the
// apply goroutine.
func TestPurgeSnapDBBeforeApply(t *testing.T) {
	if os.Getenv("F1_PURGE_CHILD") == "1" {
		purgeSnapDBBeforeApplyChild(t)
		return
	}
	cmd := exec.Command(os.Args[0], "-test.run", "^TestPurgeSnapDBBeforeApply$", "-test.v", "-test.count=1")
	cmd.Env = append(os.Environ(), "F1_PURGE_CHILD=1")
	out, err := cmd.CombinedOutput()
	if err != nil && strings.Contains(string(out), "failed to open snapshot backend") {
		i := strings.Index(string(out), "panic: failed to open snapshot backend")
		if i < 0 {
			i = strings.Index(string(out), "failed to open snapshot backend")
		}
		end := i + 300
		if end > len(out) {
			end = len(out)
		}
		t.Fatalf("the apply loop panicked: the purge removed the pending snapshot's .snap.db:\n%s", out[i:end])
	}
	if err != nil {
		t.Fatalf("child failed otherwise: %v\n%s", err, out)
	}
}

func purgeSnapDBBeforeApplyChild(t *testing.T) {
	revertFunc := verify.DisableVerifications()
	defer revertFunc()

	lg := zap.NewExample()
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

	// six received snapshots' .snap.db files (more than maxSnapDBFiles = 5)
	for _, i := range []uint64{2, 4, 6, 8, 10, 12} {
		_, err := ss.SaveDBFrom(bytes.NewReader(db), i)
		require.NoError(t, err)
	}
	snap2Path := filepath.Join(snapdir, fmt.Sprintf("%016x.snap.db", 2))

	s.start()
	defer s.Stop()

	// hold applySnapshot of snapshot 2 before it opens the snapshot's backend
	s.bemu.RLock()
	n.readyc <- raft.Ready{Snapshot: snapMeta(2)}

	// the purge goroutine Start attaches (s.start does not)
	s.GoAttach(s.purgeFile)

	deadline := time.Now().Add(10 * time.Second)
	for fileutil.Exist(snap2Path) {
		if time.Now().After(deadline) {
			s.bemu.RUnlock()
			t.Logf("the purge kept %s", snap2Path)
			return
		}
		time.Sleep(time.Millisecond)
	}
	t.Logf("purged %s before applySnapshot opened it", snap2Path)
	s.bemu.RUnlock()

	select {
	case <-s.applyWait.Wait(2):
		t.Logf("the apply loop applied snapshot 2")
	case <-time.After(10 * time.Second):
		t.Fatalf("the apply loop did not apply snapshot 2")
	}
}
