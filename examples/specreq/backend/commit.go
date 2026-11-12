package backend

import (
	"os"

	"go.uber.org/zap"

	"go.etcd.io/etcd/server/v3/storage/backend"
	"go.etcd.io/etcd/server/v3/storage/schema"
)

// REQ backend/reopen: Close commits what the batch holds, and a backend reopened over the file
// reads every write made before the close, also after creating its bucket again as boot does (a
// restarting member).
// Users: etcdserver/server.go:957 (Cleanup's Close), etcdserver/bootstrap.go:259, :266
// (OpenBackend over the data directory, then schema.CreateMetaBucket on the existing file).
func ReqReopen() {
	be := openWith("specreq-backend-reopen.db", schema.Meta)
	put(be, schema.Meta, "k", "v")
	if be.Close() != nil {
		panic("reopen: Close failed")
	}
	be = openWith("specreq-backend-reopen.db", schema.Meta)
	if get(be.ReadTx(), schema.Meta, "k") != "v" {
		panic("reopen: the reopened backend lost a write made before the close")
	}
	be.Close()
}

// REQ backend/force-commit-durable: a write unlocked before ForceCommit returns survives a crash
// after it. A crash target: ReqForceCommitDurable, then ReqForceCommitRecover after any crash
// (also one during a recovery), does not panic. The marker file, created after ForceCommit
// returns, records that it did; the directory is synced after the backend's file is created, so
// that the file's name survives (bbolt does not sync it,
// nonissues/etcd-backend-name-lost-restart-panic.md).
// Users: storage/mvcc/kvstore.go:213-216 (the scheduled compaction committed before it runs),
// :289 (Commit, before the merged snapshot: etcdserver/snapshot_merge.go:36), lease/lessor.go:834,
// etcdserver/v3_server.go:412.
func ReqForceCommitDurable() {
	be := openWith("specreq-backend-durable.db", schema.Meta)
	if d, err := os.Open("."); err != nil || d.Sync() != nil || d.Close() != nil {
		return
	}
	put(be, schema.Meta, "k", "v")
	be.ForceCommit()
	if f, err := os.Create("specreq-backend-durable.marker"); err == nil {
		f.Close()
	}
	be.Close()
}

// ReqForceCommitRecover is ReqForceCommitDurable's recovery: once the marker exists, the backend
// holds the write.
func ReqForceCommitRecover() {
	if _, err := os.Stat("specreq-backend-durable.marker"); err != nil {
		return // ForceCommit may not have returned
	}
	be := openWith("specreq-backend-durable.db")
	if get(be.ReadTx(), schema.Meta, "k") != "v" {
		panic("force-commit-durable: a crash lost a write committed by ForceCommit")
	}
	be.Close()
}

// REQ backend/hook-writes: the pre-commit hook's writes are in the commit, and a read begun after
// the commit sees them (the consistent index the server's hooks save).
// Users: storage/hooks.go:45-54 (BackendHooks.OnPreCommitUnsafe: UnsafeSave of the consistent
// index, the pending configuration), etcdserver/cindex/cindex.go:107 (the index read back through
// the ReadTx).
func ReqHookWrites() {
	be := openBackend(zap.NewNop(), "specreq-backend-hook.db", backend.NewHooks(func(tx backend.UnsafeReadWriter) {
		tx.UnsafePut(schema.Meta, []byte("k"), []byte("v"))
	}))
	tx := be.BatchTx()
	tx.LockOutsideApply()
	tx.UnsafeCreateBucket(schema.Meta)
	tx.Unlock()
	be.ForceCommit()
	if get(be.ReadTx(), schema.Meta, "k") != "v" {
		panic("hook-writes: the hook's write is not visible after the commit")
	}
	be.Close()
}
