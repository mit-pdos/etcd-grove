// Package backend holds the requirement snippets of etcd's storage backend
// (go.etcd.io/etcd/server/v3/storage/backend): what its users (mvcc, the lessor, auth, membership,
// alarms, the consistent index and the server's hooks, the server's snapshot and shutdown) rely on.
//
// Each snippet ReqXxx is a closed program, an adequacy target: it opens a backend on a new file of
// its own (a relative path in the current directory), uses the API as the callers do, and panics
// where what a caller relies on fails. Its requirement is that it does not panic.
//
// Every snippet assumes: no file at its paths when it starts, and no other process touches them;
// no crash (except where a snippet says it is a crash target); the environment variable
// ETCD_VERIFY is unset (set, the backend panics on callers it does not expect, such as
// LockInsideApply outside the server's apply). A failure of the file system the snippet itself
// calls ends the snippet without a panic: it is not the backend's.
package backend

import (
	"go.uber.org/zap"

	"go.etcd.io/etcd/server/v3/storage/backend"
	"go.etcd.io/etcd/server/v3/storage/schema"
)

// openBackend opens a backend over the file at path.
func openBackend(lg *zap.Logger, path string, hooks backend.Hooks) backend.Backend {
	cfg := backend.DefaultBackendConfig(lg)
	cfg.Path = path
	cfg.Hooks = hooks
	return backend.New(cfg)
}

// openWith opens a backend over the file at path, with no hooks, and creates the buckets bs in
// one session, as boot does (schema.CreateMetaBucket, CreateAlarmBucket, ...).
func openWith(path string, bs ...backend.Bucket) backend.Backend {
	be := openBackend(zap.NewNop(), path, nil)
	tx := be.BatchTx()
	tx.LockOutsideApply()
	for _, b := range bs {
		tx.UnsafeCreateBucket(b)
	}
	tx.Unlock()
	return be
}

// put writes k = v in a session of its own (as schema's MustPutAlarm, UnsafeSave...).
func put(be backend.Backend, b backend.Bucket, k, v string) {
	tx := be.BatchTx()
	tx.LockOutsideApply()
	tx.UnsafePut(b, []byte(k), []byte(v))
	tx.Unlock()
}

// value is the value of a single-key read: "" if the key is absent (the snippets put no empty
// value).
func value(vs [][]byte) string {
	switch len(vs) {
	case 0:
		return ""
	case 1:
		return string(vs[0])
	}
	panic("a single-key read returned several entries")
}

// get reads k with a single-key read (a nil end) on rt, read-locked. A ConcurrentReadTx ends at
// its RUnlock (the next RUnlock panics), so get reads one key of it at most.
func get(rt backend.ReadTx, b backend.Bucket, k string) string {
	rt.RLock()
	defer rt.RUnlock()
	_, vs := rt.UnsafeRange(b, []byte(k), nil, 0)
	return value(vs)
}

// getBatch reads k with a single-key read in a session of its own.
func getBatch(be backend.Backend, b backend.Bucket, k string) string {
	tx := be.BatchTx()
	tx.LockOutsideApply()
	defer tx.Unlock()
	_, vs := tx.UnsafeRange(b, []byte(k), nil, 0)
	return value(vs)
}

// REQ backend/write-then-read: a session's put is read, after its Unlock, by a ConcurrentReadTx, by
// the shared ReadTx and by the next session.
// Users: storage/schema/alarm.go:52-57 then :84-93 (MustPutAlarm, then GetAllAlarms on the
// ReadTx), storage/mvcc/kvstore_txn.go:259 then :55-60, :126 (a write transaction's put, then
// Read's ConcurrentReadTx and its single-key range), :174-177, :189 (a later write transaction's
// Range on the batch), storage/schema/cindex.go:40, auth_users.go:57 (single-key reads, nil end).
func ReqWriteThenRead() {
	be := openWith("specreq-backend-write-read.db", schema.Alarm)
	put(be, schema.Alarm, "k", "v")
	if get(be.ConcurrentReadTx(), schema.Alarm, "k") != "v" || get(be.ReadTx(), schema.Alarm, "k") != "v" ||
		getBatch(be, schema.Alarm, "k") != "v" {
		panic("write-then-read: a read begun after Unlock missed the write")
	}
	be.Close()
}

// REQ backend/delete-visible: a key deleted in a session that also put another key is gone for the
// shared ReadTx after the session's Unlock, and the other key is there (Unlock commits a session
// that deleted: etcd-io/etcd#17119). Not through a ConcurrentReadTx, whose copy of the read buffer
// may predate the commit (nonissues/etcd-backend-read-buffer-cache-stale-after-commit.md).
// Users: storage/mvcc/kvstore_compaction.go:58-71 (deletes and the finished-compaction put in one
// session), storage/schema/auth_users.go:49 (a user deleted, then the auth revision put),
// alarm.go:81 then :84-88 (MustDeleteAlarm, then GetAllAlarms on the ReadTx).
func ReqDeleteVisible() {
	be := openWith("specreq-backend-delete.db", schema.Alarm)
	put(be, schema.Alarm, "k", "v")
	tx := be.BatchTx()
	tx.LockOutsideApply()
	tx.UnsafeDelete(schema.Alarm, []byte("k"))
	tx.UnsafePut(schema.Alarm, []byte("k2"), []byte("v"))
	tx.Unlock()
	if get(be.ReadTx(), schema.Alarm, "k") != "" || get(be.ReadTx(), schema.Alarm, "k2") != "v" {
		panic("delete-visible: the deleted key is still read, or the session's put is missing")
	}
	be.Close()
}

// REQ backend/lent-write: a callee writes through be.BatchTx() inside its caller's session (the
// caller holds the lock); the caller's view of its own keys is unchanged, and the callee's write
// is in the session (the lessor's lease delete inside mvcc's write transaction).
// Users: lease/lessor.go:343, :359-361 (Revoke: UnsafeDeleteLease on le.b.BatchTx() inside the
// range deleter's transaction, storage/mvcc/kvstore_txn.go:174-177), storage/schema/lease.go:58.
func ReqLentWrite() {
	be := openWith("specreq-backend-lent.db", schema.Key, schema.Lease)
	put(be, schema.Lease, "id", "l")
	tx := be.BatchTx()
	tx.LockInsideApply()
	tx.UnsafeSeqPut(schema.Key, []byte("k"), []byte("v"))
	be.BatchTx().UnsafeDelete(schema.Lease, []byte("id")) // the callee, under the caller's lock
	_, vs := tx.UnsafeRange(schema.Key, []byte("k"), nil, 0)
	tx.Unlock()
	if value(vs) != "v" || get(be.ReadTx(), schema.Lease, "id") != "" {
		panic("lent-write: the callee's write changed the caller's keys, or is not in the session")
	}
	be.Close()
}

// REQ backend/bare-rlock: the shared ReadTx may be read-locked and unlocked with nothing read, also
// after the backend's Close (mvcc's Rev() from the compactor), and Size and SizeInUse may be read
// after Close (the metrics reporter).
// Users: storage/mvcc/kv_view.go:32-35 (Rev: Read and End, kvstore_txn.go:60, :162, RLock and
// RUnlock), etcdserver/server.go:957-961 (Cleanup closes the backend, then stops the compactor,
// whose api/v3compactor/revision.go:81 calls Rev), storage/mvcc/kvstore.go:521-527 (the metrics'
// Size and SizeInUse).
func ReqBareRLock() {
	be := openWith("specreq-backend-bare-rlock.db")
	be.ReadTx().RLock()
	be.ReadTx().RUnlock()
	be.Close()
	be.ReadTx().RLock()
	be.ReadTx().RUnlock()
	_, _ = be.Size(), be.SizeInUse()
}
