package etcdserver

import (
	"testing"

	"github.com/stretchr/testify/require"
	"go.uber.org/zap/zaptest"

	"go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/pkg/v3/pbutil"
	"go.etcd.io/etcd/server/v3/config"
	"go.etcd.io/etcd/server/v3/etcdserver/cindex"
	"go.etcd.io/etcd/server/v3/storage/wal"
	"go.etcd.io/etcd/server/v3/storage/wal/walpb"
	"go.etcd.io/raft/v3"
	"go.etcd.io/raft/v3/raftpb"
)

func TestBootstrapWALFromSnapshotBackendAheadOfWAL(t *testing.T) {
	dataDir, err := createDataDir(t)
	require.NoError(t, err)

	cfg := config.ServerConfig{
		Logger:          zaptest.NewLogger(t),
		DataDir:         dataDir,
		ForceNewCluster: true,
	}

	var ents []*raftpb.Entry
	for idx := uint64(28); idx <= 31; idx++ {
		ents = append(ents, &raftpb.Entry{
			Type:  raftpb.EntryNormal.Enum(),
			Data:  []byte("foo"),
			Term:  new(uint64(2)),
			Index: new(idx),
		})
	}

	metadata := pbutil.MustMarshalMessage(
		&etcdserverpb.Metadata{
			NodeID:    new(uint64(1)),
			ClusterID: new(uint64(1)),
		},
	)
	w, err := wal.Create(cfg.Logger, cfg.WALDir(), metadata)
	require.NoError(t, err)
	snapshot := &raftpb.Snapshot{
		Metadata: &raftpb.SnapshotMetadata{
			ConfState: &raftpb.ConfState{Voters: []uint64{1, 2, 3}},
			Index:     new(uint64(27)),
			Term:      new(uint64(2)),
		},
	}
	require.NoError(t, w.SaveSnapshot(&walpb.Snapshot{
		Index:     snapshot.Metadata.Index,
		Term:      snapshot.Metadata.Term,
		ConfState: snapshot.Metadata.ConfState,
	}))
	err = w.Save(&raftpb.HardState{Term: new(uint64(2)), Commit: new(uint64(28))}, ents)
	require.NoError(t, err)
	require.NoError(t, w.Close())

	bwal := bootstrapWALFromSnapshot(cfg, snapshot, cindex.NewFakeConsistentIndex(49))

	allEnts := bwal.ents
	require.NotEmpty(t, allEnts)
	for i := 1; i < len(allEnts); i++ {
		require.Equalf(t, allEnts[i-1].GetIndex()+1, allEnts[i].GetIndex(), "entries must be contiguous at position %d", i)
	}
	require.Equal(t, allEnts[len(allEnts)-1].GetIndex(), bwal.st.GetCommit(), "commit index must not exceed the last entry index")

	var fillerCount int
	for _, e := range allEnts {
		if e.GetIndex() >= 32 && e.GetIndex() <= 49 {
			fillerCount++
			require.Equal(t, raftpb.EntryNormal, e.GetType())
			require.Empty(t, e.Data)
		}
	}
	require.Equal(t, 18, fillerCount)

	last := allEnts[len(allEnts)-1]
	require.Equal(t, raftpb.EntryConfChange, last.GetType())

	// Also verify that bwal.MemoryStorage() succeeds without panicking and has lastIndex == 51.
	ms := bwal.MemoryStorage()
	lastIdx, err := ms.LastIndex()
	require.NoError(t, err)
	require.Equal(t, uint64(51), lastIdx)

	require.NoError(t, bwal.w.Close())
	st2, ents2, err := func() (*raftpb.HardState, []*raftpb.Entry, error) {
		w2, err := wal.Open(cfg.Logger, cfg.WALDir(), &walpb.Snapshot{
			Index: snapshot.Metadata.Index,
			Term:  snapshot.Metadata.Term,
		})
		if err != nil {
			return nil, nil, err
		}
		defer w2.Close()
		_, st2, ents2, err := w2.ReadAll()
		return st2, ents2, err
	}()
	require.NoError(t, err)
	require.NotEmpty(t, ents2)
	for i := 1; i < len(ents2); i++ {
		require.Equalf(t, ents2[i-1].GetIndex()+1, ents2[i].GetIndex(), "WAL entries must be contiguous on disk at position %d", i)
	}
	require.Equal(t, allEnts[len(allEnts)-1].GetIndex(), ents2[len(ents2)-1].GetIndex())
	require.Equal(t, uint64(2), st2.GetTerm())

	t.Logf("in-memory bwal.st.GetCommit() = %d, on-disk st2.GetCommit() = %d, last WAL entry index = %d",
		bwal.st.GetCommit(), st2.GetCommit(), ents2[len(ents2)-1].GetIndex())
}

func TestProbePreFixMemoryStoragePanicsOnGap(t *testing.T) {
	dataDir, err := createDataDir(t)
	require.NoError(t, err)

	cfg := config.ServerConfig{
		Logger:  zaptest.NewLogger(t),
		DataDir: dataDir,
	}

	var ents []*raftpb.Entry
	for idx := uint64(28); idx <= 31; idx++ {
		ents = append(ents, &raftpb.Entry{
			Type:  raftpb.EntryNormal.Enum(),
			Data:  []byte("foo"),
			Term:  new(uint64(2)),
			Index: new(idx),
		})
	}

	metadata := pbutil.MustMarshalMessage(
		&etcdserverpb.Metadata{
			NodeID:    new(uint64(1)),
			ClusterID: new(uint64(1)),
		},
	)
	w, err := wal.Create(cfg.Logger, cfg.WALDir(), metadata)
	require.NoError(t, err)
	snapshot := &raftpb.Snapshot{
		Metadata: &raftpb.SnapshotMetadata{
			ConfState: &raftpb.ConfState{Voters: []uint64{1, 2, 3}},
			Index:     new(uint64(27)),
			Term:      new(uint64(2)),
		},
	}
	require.NoError(t, w.SaveSnapshot(&walpb.Snapshot{
		Index:     snapshot.Metadata.Index,
		Term:      snapshot.Metadata.Term,
		ConfState: snapshot.Metadata.ConfState,
	}))
	require.NoError(t, w.Save(&raftpb.HardState{Term: new(uint64(2)), Commit: new(uint64(28))}, ents))
	require.NoError(t, w.Close())

	// Reproduce pre-PR#22655 sequence (without fillBackendAheadGap):
	wOpen, st, walEnts, snap, meta := openWALFromSnapshot(cfg, snapshot)
	bwal := &bootstrappedWAL{
		lg:       cfg.Logger,
		w:        wOpen,
		st:       st,
		ents:     walEnts,
		snapshot: snap,
		meta:     meta,
		haveWAL:  true,
	}
	defer bwal.w.Close()

	bwal.st.Commit = new(max(bwal.st.GetCommit(), uint64(49)))
	bwal.ents = bwal.CommitedEntries()
	ccEntries := bwal.NewConfigChangeEntries()
	bwal.AppendAndCommitEntries(ccEntries)

	// Without fillBackendAheadGap:
	// 1. bwal.ents has [28, 29, 30, 31, 50, 51] (length 6, non-contiguous), so
	//    ms.LastIndex() = 27 + 6 = 33 != 51, and raft.RestartNode panics in loadState:
	//    "1 state.commit 51 is out of range [27, 33]"
	ms := bwal.MemoryStorage()
	lastIdx, err := ms.LastIndex()
	require.NoError(t, err)
	require.Equal(t, uint64(33), lastIdx)
	require.Panics(t, func() {
		n := raft.RestartNode(&raft.Config{
			ID:            1,
			ElectionTick:  10,
			HeartbeatTick: 1,
			Storage:       ms,
		})
		n.Stop()
	})

	// 2. And the WAL on disk is now permanently corrupted: reopening it fails with
	//    wal.ErrSliceOutOfRange ("wal: slice bounds out of range").
	require.NoError(t, bwal.w.Close())
	w2, err := wal.Open(cfg.Logger, cfg.WALDir(), &walpb.Snapshot{
		Index: snapshot.Metadata.Index,
		Term:  snapshot.Metadata.Term,
	})
	require.NoError(t, err)
	defer w2.Close()
	_, _, _, err = w2.ReadAll()
	require.ErrorIs(t, err, wal.ErrSliceOutOfRange)
}

func TestProbeMembershipChangeInBackendAheadGap(t *testing.T) {
	dataDir, err := createDataDir(t)
	require.NoError(t, err)

	cfg := config.ServerConfig{
		Logger:          zaptest.NewLogger(t),
		DataDir:         dataDir,
		ForceNewCluster: true,
	}

	// Snapshot at index 27 had voters {1, 2}.
	// Suppose at index 35 (in the gap 32..49 where the backend is ahead of the WAL),
	// node 3 was added to the cluster, so the backend at consistentIndex=49 has voters {1, 2, 3}.
	var ents []*raftpb.Entry
	for idx := uint64(28); idx <= 31; idx++ {
		ents = append(ents, &raftpb.Entry{
			Type:  raftpb.EntryNormal.Enum(),
			Data:  []byte("foo"),
			Term:  new(uint64(2)),
			Index: new(idx),
		})
	}

	metadata := pbutil.MustMarshalMessage(
		&etcdserverpb.Metadata{
			NodeID:    new(uint64(1)),
			ClusterID: new(uint64(1)),
		},
	)
	w, err := wal.Create(cfg.Logger, cfg.WALDir(), metadata)
	require.NoError(t, err)
	snapshot := &raftpb.Snapshot{
		Metadata: &raftpb.SnapshotMetadata{
			ConfState: &raftpb.ConfState{Voters: []uint64{1, 2}},
			Index:     new(uint64(27)),
			Term:      new(uint64(2)),
		},
	}
	require.NoError(t, w.SaveSnapshot(&walpb.Snapshot{
		Index:     snapshot.Metadata.Index,
		Term:      snapshot.Metadata.Term,
		ConfState: snapshot.Metadata.ConfState,
	}))
	require.NoError(t, w.Save(&raftpb.HardState{Term: new(uint64(2)), Commit: new(uint64(28))}, ents))
	require.NoError(t, w.Close())

	bwal := bootstrapWALFromSnapshot(cfg, snapshot, cindex.NewFakeConsistentIndex(49))
	defer bwal.w.Close()

	// Because fillBackendAheadGap filled 32..49 with empty EntryNormal entries,
	// GetEffectiveNodeIDsFromWALEntries only saw snapshot Voters {1, 2},
	// so only 1 EntryConfChange (removing node 2, at index 50) was generated.
	var ccCount int
	for _, e := range bwal.ents {
		if e.GetType() == raftpb.EntryConfChange {
			ccCount++
		}
	}
	require.Equal(t, 1, ccCount)
	require.Equal(t, uint64(50), bwal.ents[len(bwal.ents)-1].GetIndex())
}
