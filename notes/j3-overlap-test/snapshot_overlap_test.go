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
	"os"
	"path/filepath"
	"sync"
	"testing"
	"time"

	"github.com/stretchr/testify/require"
	"go.uber.org/zap"
	"go.uber.org/zap/zapcore"
	"go.uber.org/zap/zaptest"
	"go.uber.org/zap/zaptest/observer"

	"go.etcd.io/etcd/client/pkg/v3/types"
	"go.etcd.io/etcd/client/pkg/v3/verify"
	"go.etcd.io/etcd/pkg/v3/notify"
	"go.etcd.io/etcd/server/v3/config"
	"go.etcd.io/etcd/server/v3/etcdserver/api/membership"
	"go.etcd.io/etcd/server/v3/etcdserver/api/snap"
	"go.etcd.io/etcd/server/v3/etcdserver/api/v3alarm"
	"go.etcd.io/etcd/server/v3/etcdserver/cindex"
	"go.etcd.io/etcd/server/v3/features"
	"go.etcd.io/etcd/server/v3/lease"
	serverstorage "go.etcd.io/etcd/server/v3/storage"
	"go.etcd.io/etcd/server/v3/storage/backend"
	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
	"go.etcd.io/etcd/server/v3/storage/mvcc"
	"go.etcd.io/etcd/server/v3/storage/schema"
	"go.etcd.io/etcd/server/v3/storage/wal"
	"go.etcd.io/raft/v3"
	"go.etcd.io/raft/v3/raftpb"
)

// overlapServer is a follower server over a nop raft node (as in
// TestSnapshotDBKeptUntilOpened), with a real WAL and snapshotter, so that
// SaveSnap, Release and the snapshot's .snap.db behave as in production, and
// with snapshot-heavy settings: a disk snapshot (CreateSnapshot) after every
// SnapshotCount+1 applied entries, and a compaction (Compact) to one entry
// below the applied index after each.
type overlapServer struct {
	s     *EtcdServer
	n     *readyNode
	rs    *raft.MemoryStorage
	be    backend.Backend
	ss    *snap.Snapshotter
	db    []byte
	logs  *observer.ObservedLogs
	snapc uint64
}

func newOverlapServer(t *testing.T, snapshotCount uint64) *overlapServer {
	core, logs := observer.New(zapcore.DebugLevel)
	lg := zap.New(zapcore.NewTee(core, zaptest.NewLogger(t, zaptest.Level(zapcore.InfoLevel)).Core()))
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
	alarmStore, err := v3alarm.NewAlarmStore(lg, schema.NewAlarmBackend(lg, be))
	require.NoError(t, err)
	s := &EtcdServer{
		lgMu: new(sync.RWMutex),
		lg:   lg,
		Cfg: config.ServerConfig{
			Logger:                 lg,
			DataDir:                testdir,
			SnapshotCount:          snapshotCount,
			SnapshotCatchUpEntries: 1,
			ServerFeatureGate:      features.NewDefaultServerFeatureGate("test", lg),
		},
		r:                 *r,
		snapshotter:       ss,
		cluster:           cl,
		consistIndex:      ci,
		beHooks:           serverstorage.NewBackendHooks(lg, ci),
		firstCommitInTerm: notify.NewNotifier(),
		lessor:            &lease.FakeLessor{},
		alarmStore:        alarmStore,
	}
	s.kv = mvcc.New(lg, be, &lease.FakeLessor{}, mvcc.StoreConfig{})
	s.be = be
	be.ForceCommit()
	db, err := os.ReadFile(bePath)
	require.NoError(t, err)
	return &overlapServer{s: s, n: n, rs: rs, be: be, ss: ss, db: db, logs: logs}
}

// entries sends a Ready that appends and commits the no-op entries lo..hi.
func (o *overlapServer) entries(lo, hi uint64) {
	var ents []*raftpb.Entry
	for i := lo; i <= hi; i++ {
		ents = append(ents, &raftpb.Entry{Index: new(i), Term: new(uint64(1))})
	}
	o.n.readyc <- raft.Ready{Entries: ents, CommittedEntries: ents}
}

// snapshot sends a Ready with a snapshot at index i, its .snap.db saved first,
// as rafthttp saves it on receipt of a MsgSnap.
func (o *overlapServer) snapshot(t *testing.T, i uint64) {
	_, err := o.ss.SaveDBFrom(bytes.NewReader(o.db), i)
	require.NoError(t, err)
	o.n.readyc <- raft.Ready{Snapshot: &raftpb.Snapshot{Metadata: &raftpb.SnapshotMetadata{
		Index:     new(i),
		Term:      new(uint64(1)),
		ConfState: &raftpb.ConfState{Voters: []uint64{1}},
	}}}
}

func (o *overlapServer) waitApplied(t *testing.T, i uint64) {
	select {
	case <-o.s.applyWait.Wait(i):
	case <-time.After(10 * time.Second):
		t.Fatalf("index %d not applied", i)
	}
}

// logged counts the log entries with the message msg and the field key = v.
func (o *overlapServer) logged(msg, key string, v uint64) int {
	return o.logs.FilterMessage(msg).FilterField(zap.Uint64(key, v)).Len()
}

// TestSnapshotOverlapApplySnapshotFirst: raftNode's ApplySnapshot of an
// incoming snapshot runs while the apply job of the previous Ready is about to
// snapshot and compact (the FIFO scheduler does not wait for the job before
// raftNode handles the next Ready). The job's CreateSnapshot(appliedi) then
// finds the newer snapshot (ErrSnapOutOfDate) and its Compact finds the log
// compacted past its index (ErrCompacted); both are tolerated: no snapshot is
// saved at the job's index, nothing panics, and the storage keeps the incoming
// snapshot.
func TestSnapshotOverlapApplySnapshotFirst(t *testing.T) {
	revertFunc := verify.DisableVerifications()
	defer revertFunc()

	const n, m = uint64(10), uint64(20)
	o := newOverlapServer(t, 3)
	o.s.start()
	defer o.s.Stop()

	// hold the apply job before its disk snapshot: its KV().Commit() takes the
	// backend's batch transaction lock
	tx := o.be.BatchTx()
	tx.Lock()
	held := true
	defer func() {
		if held {
			tx.Unlock()
		}
	}()

	o.entries(1, n)
	o.waitApplied(t, n)
	o.snapshot(t, m)

	// wait for raftNode's ApplySnapshot(m)
	deadline := time.Now().Add(10 * time.Second)
	for {
		fi, err := o.rs.FirstIndex()
		require.NoError(t, err)
		if fi == m+1 {
			break
		}
		if time.Now().After(deadline) {
			t.Fatalf("raftNode did not apply the snapshot to its storage")
		}
		time.Sleep(time.Millisecond)
	}
	require.Equal(t, 0, o.logged("saved snapshot to disk", "snapshot-index", n),
		"the job snapshotted before raftNode's ApplySnapshot: no overlap")

	tx.Unlock()
	held = false
	o.waitApplied(t, m)

	// the job did try to snapshot at n, after ApplySnapshot(m)
	deadline = time.Now().Add(10 * time.Second)
	for o.logged("triggering snapshot", "local-member-applied-index", n) == 0 {
		if time.Now().After(deadline) {
			t.Fatalf("the apply job did not snapshot at %d", n)
		}
		time.Sleep(time.Millisecond)
	}
	// CreateSnapshot(n) returned ErrSnapOutOfDate (no snapshot saved at n), and
	// Compact(n-1) returned ErrCompacted (no compaction logged)
	require.Equal(t, 0, o.logged("saved snapshot to disk", "snapshot-index", n))
	require.Equal(t, 0, o.logged("compacted Raft logs", "compact-index", n-1))
	sn, err := o.rs.Snapshot()
	require.NoError(t, err)
	require.Equal(t, m, sn.Metadata.GetIndex())
	fi, err := o.rs.FirstIndex()
	require.NoError(t, err)
	require.Equal(t, m+1, fi)
}

// TestSnapshotOverlapCreateSnapshotFirst: the other order, the job's
// CreateSnapshot and Compact before raftNode's ApplySnapshot of a newer
// snapshot, which then replaces the job's.
func TestSnapshotOverlapCreateSnapshotFirst(t *testing.T) {
	revertFunc := verify.DisableVerifications()
	defer revertFunc()

	const n, m = uint64(10), uint64(20)
	o := newOverlapServer(t, 3)
	o.s.start()
	defer o.s.Stop()

	o.entries(1, n)
	deadline := time.Now().Add(10 * time.Second)
	for o.logged("compacted Raft logs", "compact-index", n-1) == 0 {
		if time.Now().After(deadline) {
			t.Fatalf("the apply job did not compact at %d", n-1)
		}
		time.Sleep(time.Millisecond)
	}
	require.Equal(t, 1, o.logged("saved snapshot to disk", "snapshot-index", n))
	o.snapshot(t, m)
	o.waitApplied(t, m)
	sn, err := o.rs.Snapshot()
	require.NoError(t, err)
	require.Equal(t, m, sn.Metadata.GetIndex())
}

// TestSnapshotOverlapStress: batches of entries, each followed at once by a
// newer snapshot, with no synchronization between the Readies, so that the
// apply job's CreateSnapshot/Compact and raftNode's ApplySnapshot interleave
// as the scheduler has them (run with -race).
func TestSnapshotOverlapStress(t *testing.T) {
	revertFunc := verify.DisableVerifications()
	defer revertFunc()

	o := newOverlapServer(t, 2)
	o.s.start()
	defer o.s.Stop()

	next := uint64(1)
	const rounds, batch, gap = 200, 8, 3
	for r := 0; r < rounds; r++ {
		o.entries(next, next+batch-1)
		next += batch
		if r%2 == 0 {
			// a snapshot past the batch, at once
			i := next - 1 + gap
			o.snapshot(t, i)
			next = i + 1
		}
	}
	o.waitApplied(t, next-1)

	outOfDate := 0
	for _, e := range o.logs.FilterMessage("triggering snapshot").All() {
		ai := uint64(e.ContextMap()["local-member-applied-index"].(uint64))
		if o.logged("saved snapshot to disk", "snapshot-index", ai) == 0 {
			outOfDate++
		}
	}
	t.Logf("disk snapshots triggered: %d, of which out of date (ErrSnapOutOfDate): %d; snapshots applied: %d",
		o.logs.FilterMessage("triggering snapshot").Len(), outOfDate,
		o.logs.FilterMessage("applied incoming Raft snapshot").Len())
}
