package backend

import (
	"bytes"
	"os"

	"go.uber.org/zap"

	"go.etcd.io/etcd/server/v3/storage/backend"
	"go.etcd.io/etcd/server/v3/storage/schema"
)

// REQ backend/snapshot-stream: a snapshot streams a committed image's database file: WriteTo
// writes Size bytes and succeeds into a writer that accepts them; Close returns nil (the merged
// snapshot's reader, and the maintenance server's Snapshot).
// Users: server/etcdserver/snapshot_merge.go:37-70 (createMergedSnapshotMessage,
// newSnapshotReaderCloser: WriteTo into a pipe, then Close), server/etcdserver/api/v3rpc/
// maintenance.go:146-190 (Snapshot: Size, WriteTo, Close).
// Assumes: a reader slot; the backend is open; the writer never fails (a bytes.Buffer).
// Specs: backend.Snapshot.spec (beSnapN: the size n < 2^48; beHistLb_nil for its lower bound),
// snapshot.Size.spec (n), snapshot.WriteTo.spec (some bytes of the image, of length n; writeOk of
// a bytes.Buffer), snapshot.Close.spec.
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

// REQ backend/snapshot-fresh: a snapshot taken after a commit holds that commit's writes (or
// later ones): the merged snapshot (KV().Commit(), then Snapshot()) is sent as the image at the
// applied index, so it must not be an older commit's image (verify-round A10-completeness F1).
// Users: server/etcdserver/snapshot_merge.go:36-37 (s.KV().Commit(), then s.be.Snapshot(), sent at
// snapi), the receiver's applySnapshot/OpenSnapshotBackend (the image opened as the backend's).
// Assumes: the caller owns the Alarm bucket's cells and no one deletes k; its commit step records
// each committed image in its history (commitOk), whose lower bound it takes after ForceCommit
// (beHist_lb); dbPath names no file (os.WriteFile creates it, durable: Perennial's OsFs, assumed);
// a reader slot; the writer never fails (a bytes.Buffer, writeOk).
// Specs: UnsafePut.spec, Unlock.spec, backend.ForceCommit.spec (beReq: the committed image holds
// k = v), beHist_lb, backend.Snapshot.spec (beHistLb: an image no older than that commit's),
// snapshot.WriteTo.spec (some bytes of the image: imgBytes), snapshot.Close.spec, beFile_bytes
// (Durable.lean: a file of an image's bytes is a backend file of it), New.spec,
// readTx.RLock.spec, readTx.UnsafeRange.spec.
func ReqSnapshotFresh(lg *zap.Logger, be backend.Backend, dbPath string, k, v []byte) {
	tx := be.BatchTx()
	tx.LockOutsideApply()
	tx.UnsafePut(schema.Alarm, k, v)
	tx.Unlock()
	be.ForceCommit()

	snap := be.Snapshot()
	var buf bytes.Buffer
	if _, err := snap.WriteTo(&buf); err != nil {
		panic("snapshot-fresh: WriteTo into a buffer failed")
	}
	if err := snap.Close(); err != nil {
		panic("snapshot-fresh: Close failed")
	}
	if err := os.WriteFile(dbPath, buf.Bytes(), 0o600); err != nil {
		return // the environment's failure, not the backend's
	}

	be2 := backend.NewDefaultBackend(lg, dbPath)
	rt := be2.ReadTx()
	rt.RLock()
	_, vs := rt.UnsafeRange(schema.Alarm, k, nil, 0)
	rt.RUnlock()
	if len(vs) != 1 || !bytes.Equal(vs[0], v) {
		panic("snapshot-fresh: the snapshot lost a write committed before it")
	}
	be2.Close()
}
