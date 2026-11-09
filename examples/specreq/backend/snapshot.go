package backend

import (
	"bytes"

	"go.etcd.io/etcd/server/v3/storage/backend"
)

// REQ backend/snapshot-stream: a snapshot streams a committed image's database file: WriteTo
// writes Size bytes and succeeds into a writer that accepts them; Close returns nil (the merged
// snapshot's reader, and the maintenance server's Snapshot).
// Users: server/etcdserver/snapshot_merge.go:37-70 (createMergedSnapshotMessage,
// newSnapshotReaderCloser: WriteTo into a pipe, then Close), server/etcdserver/api/v3rpc/
// maintenance.go:146-190 (Snapshot: Size, WriteTo, Close).
// Assumes: a reader slot; the backend is open; the writer never fails (a bytes.Buffer).
// Specs: backend.Snapshot.spec (beCommitted, imgBytes), snapshot.Size.spec, snapshot.WriteTo.spec
// (writeOk of a bytes.Buffer), snapshot.Close.spec, imgBytes_size.
func ReqSnapshotStream(be backend.Backend) []byte {
	snap := be.Snapshot()
	size := snap.Size()
	if size < 0 || size >= 1<<62 {
		panic("snapshot-stream: a snapshot's size out of range")
	}
	var buf bytes.Buffer
	n, err := snap.WriteTo(&buf)
	if err != nil || n != size || int64(buf.Len()) != size {
		panic("snapshot-stream: WriteTo did not write the snapshot's bytes")
	}
	if err := snap.Close(); err != nil {
		panic("snapshot-stream: Close failed")
	}
	return buf.Bytes()
}
