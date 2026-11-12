package wal

import (
	"path/filepath"
	"testing"

	"github.com/stretchr/testify/require"
	"go.uber.org/zap/zaptest"

	"go.etcd.io/etcd/server/v3/storage/wal/walpb"
	"go.etcd.io/raft/v3/raftpb"
)

// A write-mode ReadAll at a snapshot with no record in the WAL sets ErrSnapshotNotFound, then
// overwrites it with newFileEncoder's nil error, and succeeds. The test fails while the bug is there.
func TestReadAllSnapshotNotFound(t *testing.T) {
	dir := filepath.Join(t.TempDir(), "w")
	lg := zaptest.NewLogger(t)
	w, err := Create(lg, dir, []byte("md"))
	require.NoError(t, err)
	for i := uint64(1); i <= 5; i++ {
		require.NoError(t, w.Save(&raftpb.HardState{Term: new(uint64(1)), Commit: new(i)}, []*raftpb.Entry{{Index: new(i), Term: new(uint64(1))}}))
	}
	require.NoError(t, w.Close())
	w, err = Open(lg, dir, &walpb.Snapshot{Index: new(uint64(3)), Term: new(uint64(1))})
	require.NoError(t, err)
	defer w.Close()
	_, _, ents, err := w.ReadAll()
	t.Logf("ReadAll at an unrecorded snapshot (3,1): err=%v, %d entries", err, len(ents))
	require.ErrorIs(t, err, ErrSnapshotNotFound)
}
