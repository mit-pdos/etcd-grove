package backend

import (
	"os"

	"go.etcd.io/etcd/server/v3/storage/schema"
)

// REQ backend/snapshot: a snapshot taken after a commit is a database file holding that commit's
// writes: WriteTo writes Size bytes and succeeds, Close succeeds, and a backend opened over a file
// of those bytes (synced, with its directory, as the receiver does) reads the writes.
// Users: etcdserver/snapshot_merge.go:36-37, :59, :74 (Commit, Snapshot, WriteTo into a pipe,
// Close), etcdserver/api/v3rpc/maintenance.go:146-156 (Snapshot, WriteTo, Close),
// etcdserver/api/snap/db.go:40-76 (SaveDBFrom: the bytes written to a file, synced, renamed, the
// directory synced), storage/backend.go:63-71 (OpenSnapshotBackend: the file opened as the backend).
func ReqSnapshot() {
	be := openWith("specreq-backend-snapshot.db", schema.Alarm)
	put(be, schema.Alarm, "k", "v")
	be.ForceCommit()
	snap := be.Snapshot()
	f, err := os.Create("specreq-backend-snapshot-copy.db")
	if err != nil {
		return
	}
	n, err := snap.WriteTo(f)
	if err != nil {
		return // the copy's write failed
	}
	if n != snap.Size() || snap.Close() != nil {
		panic("snapshot: WriteTo did not write the snapshot's Size bytes, or Close failed")
	}
	be.Close()
	if f.Sync() != nil || f.Close() != nil {
		return
	}
	if d, err := os.Open("."); err != nil || d.Sync() != nil || d.Close() != nil {
		return
	}
	be = openWith("specreq-backend-snapshot-copy.db")
	if get(be.ReadTx(), schema.Alarm, "k") != "v" {
		panic("snapshot: the snapshot's file lost a write committed before it")
	}
	be.Close()
}
