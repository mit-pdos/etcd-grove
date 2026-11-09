package backend

import (
	"bytes"

	"go.uber.org/zap"

	"go.etcd.io/etcd/server/v3/storage/backend"
	"go.etcd.io/etcd/server/v3/storage/schema"
)

// REQ backend/reopen: what a closed backend's file holds is its last commit, and Close commits
// whatever the batch holds: a backend reopened over the file reads every write made before the
// close (a restarting member, or a stopped one's disk).
// Users: server/etcdserver/bootstrap.go:240 (OpenBackend over the data directory at boot) after
// server.go's Cleanup (the backend's Close), etcdutl's offline tools.
// Assumes: the caller owns the Alarm bucket's cells; nothing else uses the backend; no crash
// (a crash leaves the file at one of the committed images: beHist); the caller owns the file's
// closed state and revert state (beFile path o, beRevs path os: a file the first open creates has
// no durable name, which the open's update records as none in the revert list, so Close gives
// beFile path (some I) for it too and the second open is 4c's boltReopen_alloc: second crash pass,
// G-a; it was a durable-name assumption, verify-round F-raft-storage F2).
// Specs: New.spec (beOpenUpd from the owned beFile), UnsafeCreateBucket.spec, UnsafePut.spec,
// Unlock.spec, backend.Close.spec (beFinal; the file through beCloseUpd from the owned beHist),
// beHist_final, beFinal_cur, readTx.RLock.spec,
// readTx.UnsafeRange.spec.
func ReqReopen(lg *zap.Logger, path string, k, v []byte) {
	be := openBackend(lg, path, nil)
	tx := be.BatchTx()
	tx.LockOutsideApply()
	tx.UnsafeCreateBucket(schema.Alarm)
	tx.UnsafePut(schema.Alarm, k, v)
	tx.Unlock()
	if err := be.Close(); err != nil {
		panic("reopen: close failed")
	}

	be2 := openBackend(lg, path, nil)
	rt := be2.ReadTx()
	rt.RLock()
	_, vs := rt.UnsafeRange(schema.Alarm, k, nil, 0)
	rt.RUnlock()
	if len(vs) != 1 || !bytes.Equal(vs[0], v) {
		panic("reopen: the reopened file lost a write made before the close")
	}
	be2.Close()
}

// REQ backend/force-commit: after ForceCommit, the last commit holds every write unlocked before
// it (what a crash may leave, with fsync on, is at least that commit's image): the per-call step's
// Y is beCommitted of an image holding k = v, which a reopened backend reads back (ReqReopen's).
// Users: storage/mvcc/kvstore.go:216, 289 (the scheduled compaction key committed before the
// compaction is scheduled), lease/lessor.go:834, server/etcdserver/v3_server.go:412, 2d's
// snapshot (KV().Commit()).
// Assumes: the caller's commit step records the committed image in its history (commitOk), and
// holds the history (beHist) in its invariant.
// Specs: backend.ForceCommit.spec (beReq: the per-call step gets beCommitted of the batch image
// at the commit), beCurIs_cur.
func ReqForceCommitDurable(be backend.Backend, k, v []byte) {
	tx := be.BatchTx()
	tx.LockOutsideApply()
	tx.UnsafePut(schema.Alarm, k, v)
	tx.Unlock()
	be.ForceCommit()
	rt := be.ReadTx()
	rt.RLock()
	_, vs := rt.UnsafeRange(schema.Alarm, k, nil, 0)
	rt.RUnlock()
	if len(vs) != 1 || !bytes.Equal(vs[0], v) {
		panic("force-commit: the committed image lost a write unlocked before the commit")
	}
}

// REQ backend/hook-writes: the pre-commit hook writes its cells under the commit's lock, and a
// read begun after the commit sees them (the consistent index the server's hooks save).
// Users: server/storage/hooks.go:43-52 (BackendHooks.OnPreCommitUnsafe: UnsafeSave of the
// consistent index, the pending configuration), server/etcdserver/cindex/cindex.go (the index read
// back through ReadTx).
// Assumes: the hooks own the Meta key k (published; its tracker in an invariant the hook's update
// opens and the main thread's read observes, not in the lock's resource) and write v at each
// commit; Meta exists for good (beMade); the hooks' cells untracked before the close (beVis_drop).
// Specs: New.spec (hookOk), backend.ForceCommit.spec, hooks.OnPreCommitUnsafe.spec,
// UnsafePut.spec, readTx.RLock.spec, readTx.UnsafeRange.spec.
func ReqHookWrites(lg *zap.Logger, path string, k, v []byte) {
	be := openBackend(lg, path, backend.NewHooks(func(tx backend.UnsafeReadWriter) {
		tx.UnsafePut(schema.Meta, k, v)
	}))
	tx := be.BatchTx()
	tx.LockOutsideApply()
	tx.UnsafeCreateBucket(schema.Meta)
	tx.Unlock()
	be.ForceCommit()
	rt := be.ReadTx()
	rt.RLock()
	_, vs := rt.UnsafeRange(schema.Meta, k, nil, 0)
	rt.RUnlock()
	if len(vs) != 1 || !bytes.Equal(vs[0], v) {
		panic("hook-writes: the hook's write is not visible after the commit")
	}
	be.Close()
}
