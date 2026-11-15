package etcdserverboot

import (
	"bytes"

	"go.uber.org/zap"

	"go.etcd.io/etcd/server/v3/etcdserver/api/snap"
	"go.etcd.io/raft/v3/raftpb"
)

// Go test of a trusted model (not a proof obligation: the functions it calls are trusted, or have
// no spec here); run it to check the model against the code.
// REQ etcdserverboot/snap-round-trip: a received database snapshot saved at its index is found by
// that index until a later snapshot releases it; a second save at the same index keeps the first.
// Users: rafthttp's snapshot receiver (SaveDBFrom), the apply thread's applySnapshot
// (OpenSnapshotBackend: DBFilePath, then the rename), storage.Release (ReleaseSnapDBs).
// Assumes: dir is an existing, empty snapshot directory; the disk does not fail (diskOk).
// Specs: snap.New.spec, Snapshotter.SaveDBFrom.spec, Snapshotter.DBFilePath.spec,
// Snapshotter.ReleaseSnapDBs.spec; Snap.saveAt, Snap.releaseBelow.
func ReqSnapRoundTrip(lg *zap.Logger, dir string) {
	ss := snap.New(lg, dir)
	if _, err := ss.SaveDBFrom(bytes.NewReader([]byte("db-at-5")), 5); err != nil {
		panic("snap-round-trip: save") // a bytes.Reader does not fail
	}
	if _, err := ss.DBFilePath(5); err != nil {
		panic("snap-round-trip: a saved snapshot not found")
	}
	if _, err := ss.SaveDBFrom(bytes.NewReader([]byte("other")), 5); err != nil {
		panic("snap-round-trip: second save")
	}
	if err := ss.ReleaseSnapDBs(&raftpb.Snapshot{Metadata: &raftpb.SnapshotMetadata{Index: u64(6)}}); err != nil {
		panic("snap-round-trip: release")
	}
	if _, err := ss.DBFilePath(5); err == nil {
		panic("snap-round-trip: a released snapshot still found")
	}
}
