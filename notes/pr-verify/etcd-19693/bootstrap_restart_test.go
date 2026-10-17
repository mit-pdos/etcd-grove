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
	"fmt"
	"os"
	"path/filepath"
	"testing"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
	bolt "go.etcd.io/bbolt"
	"go.uber.org/zap/zaptest"

	"go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/pkg/v3/pbutil"
	"go.etcd.io/etcd/server/v3/config"
	"go.etcd.io/etcd/server/v3/etcdserver/api/snap"
	serverstorage "go.etcd.io/etcd/server/v3/storage"
	"go.etcd.io/etcd/server/v3/storage/schema"
	"go.etcd.io/etcd/server/v3/storage/wal"
	"go.etcd.io/etcd/server/v3/storage/wal/walpb"
	"go.etcd.io/raft/v3"
	"go.etcd.io/raft/v3/raftpb"
)

// The data dir of a restarting member. Both tests build it by hand, then run the WAL and backend
// part of bootstrap (bootstrapStorageForTest, per revision) and start raft on the result, as
// NewServer does through raft.RestartNode.

var restartConfState = raftpb.ConfState{Voters: []uint64{1}}

func restartTestConfig(t *testing.T) config.ServerConfig {
	dataDir := t.TempDir()
	require.NoError(t, os.MkdirAll(filepath.Join(dataDir, "member", "snap"), 0o700))
	return config.ServerConfig{
		Name:                "restart",
		DataDir:             dataDir,
		BackendFreelistType: bolt.FreelistArrayType,
		Logger:              zaptest.NewLogger(t),
	}
}

func ents(term uint64, from, to uint64) []raftpb.Entry {
	var es []raftpb.Entry
	for i := from; i <= to; i++ {
		es = append(es, raftpb.Entry{Term: term, Index: i})
	}
	return es
}

func writeBackend(t *testing.T, cfg config.ServerConfig, index, term uint64) {
	writeBackendConfState(t, cfg, index, term, true)
}

// writeBackendConfState writes the backend's consistent index and term, and its conf state if
// withConfState (etcd persists it in the backend only since v3.5, and only when it applies a
// membership change or a snapshot).
func writeBackendConfState(t *testing.T, cfg config.ServerConfig, index, term uint64, withConfState bool) {
	be := serverstorage.OpenBackend(cfg, nil)
	tx := be.BatchTx()
	tx.Lock()
	schema.UnsafeCreateMetaBucket(tx)
	schema.UnsafeUpdateConsistentIndex(tx, index, term)
	if withConfState {
		schema.MustUnsafeSaveConfStateToBackend(cfg.Logger, tx, &restartConfState)
	}
	tx.Unlock()
	require.NoError(t, be.Close())
}

// restartRaft starts raft on the storage bootstrap built, returning the panic it raises, if any.
func restartRaft(s *raft.MemoryStorage) (p any) {
	defer func() { p = recover() }()
	_, err := raft.NewRawNode(&raft.Config{
		ID: 1, ElectionTick: 10, HeartbeatTick: 1, Storage: s,
		MaxSizePerMsg: maxSizePerMsg, MaxInflightMsgs: maxInflightMsgs,
	})
	if err != nil {
		return err
	}
	return nil
}

func newWAL(t *testing.T, cfg config.ServerConfig) *wal.WAL {
	md := pbutil.MustMarshal(&etcdserverpb.Metadata{NodeID: 1, ClusterID: 0x1000})
	w, err := wal.Create(cfg.Logger, cfg.WALDir(), md)
	require.NoError(t, err)
	return w
}

// A follower that received a snapshot (index 10) from the leader crashed after persisting it to
// the WAL and before applying its database (`<index>.snap.db`): the backend is still at its old
// consistent index 3. Restarting must recover the backend from the snapshot database (the case
// RecoverSnapshotBackend handles, and the e2e TestRecoverSnapshotBackend covers).
func TestRestartAfterSnapshotPersistedBeforeApplied(t *testing.T) {
	cfg := restartTestConfig(t)
	w := newWAL(t, cfg)
	require.NoError(t, w.Save(raftpb.HardState{Term: 1, Vote: 1, Commit: 3}, ents(1, 1, 3)))
	walSnap := walpb.Snapshot{Index: 10, Term: 2, ConfState: &restartConfState}
	require.NoError(t, w.SaveSnapshot(walSnap))
	require.NoError(t, w.Save(raftpb.HardState{Term: 2, Vote: 1, Commit: 10}, nil))
	require.NoError(t, w.Close())

	ss := snap.New(cfg.Logger, cfg.SnapDir())
	require.NoError(t, ss.SaveSnap(raftpb.Snapshot{Data: []byte("{}"), Metadata: raftpb.SnapshotMetadata{
		Index: 10, Term: 2, ConfState: restartConfState}}))
	// the leader's database, received as "%016x.snap.db"
	writeBackend(t, cfg, 10, 2)
	require.NoError(t, os.Rename(cfg.BackendPath(), filepath.Join(cfg.SnapDir(), fmt.Sprintf("%016x.snap.db", 10))))
	// the member's own database, at consistent index 3
	writeBackend(t, cfg, 3, 1)

	s, ci := bootstrapStorageForTest(t, cfg)
	assert.Equal(t, uint64(10), ci, "the backend is not recovered from the snapshot database")
	require.Nil(t, restartRaft(s))
}

// The member's consistent index (8) is past the commit index of the last HardState that reached
// the disk (5): raft persists a HardState whose only change is Commit without an fsync, while the
// backend fsyncs the applied entries (the case bootstrapWALFromSnapshot's ForceNewCluster branch
// describes). A plain restart must still work: the entries 6..8 are re-applied and skipped.
func TestRestartWithConsistentIndexPastWALCommit(t *testing.T) {
	cfg := restartTestConfig(t)
	w := newWAL(t, cfg)
	require.NoError(t, w.Save(raftpb.HardState{Term: 1, Vote: 1, Commit: 5}, ents(1, 1, 10)))
	require.NoError(t, w.Close())
	writeBackend(t, cfg, 8, 1)

	s, _ := bootstrapStorageForTest(t, cfg)
	require.Nil(t, restartRaft(s))
}

// The backend has no conf state (written before v3.5, or by a member that has not applied a
// membership change since): a plain restart must still work.
func TestRestartWithBackendWithoutConfState(t *testing.T) {
	cfg := restartTestConfig(t)
	w := newWAL(t, cfg)
	require.NoError(t, w.Save(raftpb.HardState{Term: 1, Vote: 1, Commit: 5}, ents(1, 1, 5)))
	require.NoError(t, w.Close())
	writeBackendConfState(t, cfg, 3, 1, false)

	s, _ := bootstrapStorageForTest(t, cfg)
	require.Nil(t, restartRaft(s))
}
