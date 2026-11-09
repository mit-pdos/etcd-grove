// Package backend holds the requirement snippets of etcd's storage backend (batch 4a,
// Spec/go_etcd_io/etcd/server/v3/storage/backend/): what its users (mvcc, the lessor, auth,
// membership, alarms, the consistent index and the server's hooks, the server's snapshot and
// shutdown) rely on, each a panic on its violation.
//
// Common assumptions of every snippet (round 1, S2): the backend was opened by openBackend under
// the environment premise (dbOpenOk: the file opens and maps), with ETCD_VERIFY unset (envOk) and
// the schema's buckets declared (New's Bs = schemaBkts; each schema.* value is the backend's
// bucket: bkt, from 4b's bucketAt); every put's key and value together are at most
// bboltEntryMax (2^28) bytes; the pre-commit hooks write only Meta keys none of the snippets
// tracks (beHookFp disjoint from their footprints).
package backend

import (
	"bytes"

	"go.uber.org/zap"

	"go.etcd.io/etcd/server/v3/storage/backend"
	"go.etcd.io/etcd/server/v3/storage/schema"
)

// openBackend opens a backend over the file at path (the setup of every snippet).
func openBackend(lg *zap.Logger, path string, hooks backend.Hooks) backend.Backend {
	cfg := backend.DefaultBackendConfig(lg)
	cfg.Path = path
	cfg.Hooks = hooks
	return backend.New(cfg)
}

// REQ backend/write-then-read: a session's puts are what a read transaction begun after its
// Unlock sees (the concurrent one and the shared one), and what the next session's batch reads.
// Users: storage/mvcc/kvstore_txn.go:176-259 (a write transaction, then Read's ConcurrentReadTx,
// :55), storage/schema/alarm.go:54-58 then :85-93 (a put, then GetAllAlarms on the ReadTx),
// auth/store.go (a user put under Lock, then the permission check's ReadTx).
// Assumes: the caller owns the Alarm bucket's cells and tracks their visible image (no other
// writer of them); the bucket exists; a reader slot.
// Specs: backend.BatchTx.spec, batchTxBuffered.LockInsideApply.spec (no hook) or
// LockOutsideApply.spec, UnsafePut.spec, Unlock.spec (the two updates of the caller's footprint),
// backend.ConcurrentReadTx.spec, concurrentReadTx.UnsafeRange.spec, RUnlock.spec, readTx.RLock.spec,
// readTx.UnsafeRange.spec, readTx.RUnlock.spec.
func ReqWriteThenRead(be backend.Backend, k, v []byte) {
	tx := be.BatchTx()
	tx.LockOutsideApply()
	tx.UnsafePut(schema.Alarm, k, v)
	tx.Unlock()

	rt := be.ConcurrentReadTx()
	rt.RLock()
	_, vs := rt.UnsafeRange(schema.Alarm, k, nil, 0)
	rt.RUnlock()
	if len(vs) != 1 || !bytes.Equal(vs[0], v) {
		panic("write-then-read: a concurrent read missed an unlocked write")
	}

	srt := be.ReadTx()
	srt.RLock()
	_, vs = srt.UnsafeRange(schema.Alarm, k, nil, 0)
	srt.RUnlock()
	if len(vs) != 1 || !bytes.Equal(vs[0], v) {
		panic("write-then-read: the shared read transaction missed an unlocked write")
	}

	tx.LockOutsideApply()
	_, vs = tx.UnsafeRange(schema.Alarm, k, nil, 0)
	tx.Unlock()
	if len(vs) != 1 || !bytes.Equal(vs[0], v) {
		panic("write-then-read: the next session missed the write")
	}
}

// REQ backend/delete-visible: a key deleted in a session is gone for a read begun after its
// Unlock (Unlock commits a session that deleted: etcd-io/etcd#17119), also when the same session
// put another key.
// Users: storage/mvcc/kvstore_compaction.go:56-71 (deletes and the finished-compaction put in one
// session), storage/schema/auth_users.go:49 (a user deleted, the auth revision put), alarm.go:81.
// Assumes: as ReqWriteThenRead; k is in the bucket, k2 is another key.
// Specs: UnsafeDelete.spec, UnsafePut.spec, Unlock.spec (Sess.mid, then Sess.fin at the commit),
// backend.ConcurrentReadTx.spec, concurrentReadTx.UnsafeRange.spec.
func ReqDeleteVisible(be backend.Backend, k, k2, v2 []byte) {
	tx := be.BatchTx()
	tx.LockOutsideApply()
	tx.UnsafeDelete(schema.Alarm, k)
	tx.UnsafePut(schema.Alarm, k2, v2)
	tx.Unlock()

	rt := be.ConcurrentReadTx()
	ks, _ := rt.UnsafeRange(schema.Alarm, k, nil, 0)
	ks2, _ := rt.UnsafeRange(schema.Alarm, k2, nil, 0)
	rt.RUnlock()
	if len(ks) != 0 {
		panic("delete-visible: a deleted key is still read after Unlock")
	}
	if len(ks2) != 1 {
		panic("delete-visible: the session's put is missing")
	}
}

// REQ backend/lent-write: a callee writes its own (untracked) cells under its caller's session,
// and the caller's view of its own cells is unchanged by it (the lessor's lease delete inside
// mvcc's write transaction).
// Users: lease/lessor.go:359 (UnsafeDeleteLease on le.b.BatchTx() inside the range deleter's
// transaction, storage/mvcc/kvstore_txn.go:176), storage/schema/lease.go.
// Assumes: the caller owns the Key bucket's cells (published), the callee the Lease bucket's
// (untracked: beNoVis); revKey is in Key and above every key there; id is in Lease.
// Specs: LockInsideApply.spec, UnsafeSeqPut.spec, UnsafeDelete.spec (writable: beNoVis),
// UnsafeRange.spec (btRange), Unlock.spec.
func ReqLentWrite(be backend.Backend, revKey, kv, id []byte) {
	tx := be.BatchTx()
	tx.LockInsideApply()
	tx.UnsafeSeqPut(schema.Key, revKey, kv)
	deleteLease(be, id) // the callee, under the caller's lock
	ks, _ := tx.UnsafeRange(schema.Key, revKey, nil, 0)
	tx.Unlock()
	if len(ks) != 1 {
		panic("lent-write: the callee's write changed the caller's cells")
	}
}

func deleteLease(be backend.Backend, id []byte) {
	be.BatchTx().UnsafeDelete(schema.Lease, id)
}

// REQ backend/bare-rlock: the shared read transaction may be read-locked and unlocked with nothing
// read, at any time, also after the backend's close (mvcc's Rev() from the compactor).
// Users: storage/mvcc/kv_view.go:31-35 (Rev: ReadTx().RLock(), RUnlock()), the compactor's
// goroutine after Cleanup closed the backend.
// Assumes: a reader slot (kept by the caller: the backend's close does not take slots).
// Specs: backend.ReadTx.spec, readTx.RLock.spec (empty footprint: beVis_none), readTx.RUnlock.spec.
func ReqBareRLock(be backend.Backend) {
	rt := be.ReadTx()
	rt.RLock()
	rt.RUnlock()
}
