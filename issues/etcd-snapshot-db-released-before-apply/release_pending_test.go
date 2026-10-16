// Reproduction of issues/etcd-snapshot-db-released-before-apply.md (etcd-io/etcd#18055).
//
// This test reproduces only the deletion step of the bug: ReleaseSnapDBs of a later snapshot
// deletes the .snap.db of an earlier one that applySnapshot has yet to open. The panic itself
// (applySnapshot -> "failed to open snapshot backend") needs the interleaving between
// raftNode.start and the apply goroutine, which this test does not drive.
//
// Package snap, file server/etcdserver/api/snap/release_pending_test.go of go.etcd.io/etcd
// (module go.etcd.io/etcd/server/v3), at the etcd pin of etc/goose.py: 107edf7e4 (branch
// goose-lean of upamanyus/etcd; raft v3.7.0's raftpb).
//
// Run, in server/:
//
//	GOTOOLCHAIN=go1.27.1 go test ./etcdserver/api/snap -run '^TestReleaseRemovesPendingSnapDB$' -count=1
//
// Passes at the pin, which shows the deletion: DBFilePath(17) is ErrNoDBSnapshot after
// ReleaseSnapDBs(18).
package snap

import (
	"bytes"
	"errors"
	"testing"

	"go.uber.org/zap/zaptest"

	"go.etcd.io/raft/v3/raftpb"
)

// etcd-io/etcd#18055: raftNode.start releases (deletes) every .snap.db below the
// latest Ready's snapshot index right after persisting that snapshot, while the
// apply of an earlier Ready's snapshot may not yet have opened its .snap.db.
func TestReleaseRemovesPendingSnapDB(t *testing.T) {
	ss := New(zaptest.NewLogger(t), t.TempDir())
	// two snapshots received in quick succession (rafthttp snapshotHandler)
	for _, id := range []uint64{17, 18} {
		if _, err := ss.SaveDBFrom(bytes.NewReader([]byte("db")), id); err != nil {
			t.Fatal(err)
		}
	}
	// raftNode.start, Ready with snapshot 18: storage.Release -> ReleaseSnapDBs
	if err := ss.ReleaseSnapDBs(&raftpb.Snapshot{Metadata: &raftpb.SnapshotMetadata{Index: new(uint64(18))}}); err != nil {
		t.Fatal(err)
	}
	// applySnapshot of the Ready with snapshot 17: OpenSnapshotBackend -> DBFilePath(17)
	if _, err := ss.DBFilePath(17); !errors.Is(err, ErrNoDBSnapshot) {
		t.Fatalf("expected ErrNoDBSnapshot, got %v", err)
	}
	t.Logf("DBFilePath(17) after ReleaseSnapDBs(18): %v (applySnapshot panics: failed to open snapshot backend)", ErrNoDBSnapshot)
}
