package backend

import (
	"bytes"

	"go.uber.org/zap"

	"go.etcd.io/etcd/server/v3/storage/backend"
	"go.etcd.io/etcd/server/v3/storage/schema"
)

// REQ backend/foreach: a whole-bucket visit on a read transaction visits each entry once (the
// order is two sorted runs), on the batch transaction in key order; the visitor's error stops it.
// Users: storage/schema/alarm.go:93 (GetAllAlarms on ReadTx), membership.go:98, auth_users.go:87,
// storage/mvcc/hash.go:35 (a ConcurrentReadTx), storage/schema/lease.go:33 (MustUnsafeGetAllLeases
// under LockOutsideApply).
// Assumes: the caller owns and tracks the Alarm bucket, which holds exactly the keys of want; a
// reader slot.
// Specs: readTx.RLock.spec, readTx.UnsafeForEach.spec (rdOrder), readTx.RUnlock.spec,
// LockOutsideApply.spec, batchTxBuffered.UnsafeForEach.spec (btOrder), Unlock.spec.
func ReqForEach(be backend.Backend, want map[string]bool) {
	seen := map[string]bool{}
	rt := be.ReadTx()
	rt.RLock()
	err := rt.UnsafeForEach(schema.Alarm, func(k, v []byte) error {
		if seen[string(k)] {
			panic("foreach: a key visited twice")
		}
		seen[string(k)] = true
		return nil
	})
	rt.RUnlock()
	if err != nil || len(seen) != len(want) {
		panic("foreach: the read transaction's visit missed an entry")
	}

	var last []byte
	tx := be.BatchTx()
	tx.LockOutsideApply()
	err = tx.UnsafeForEach(schema.Alarm, func(k, v []byte) error {
		if last != nil && bytes.Compare(last, k) >= 0 {
			panic("foreach: the batch's visit is not in key order")
		}
		last = append([]byte(nil), k...)
		return nil
	})
	tx.Unlock()
	if err != nil {
		panic("foreach: the visitor returned no error")
	}
}

// REQ backend/compaction-batch: the compaction's batches: with the safe-range lock, a limited
// batch range of Key, deletes of what it returned, and (last batch) the finished-compaction key
// put in the same session; after Unlock the deleted keys are gone and the key is set.
// Users: storage/mvcc/kvstore_compaction.go:31-95 (scheduleCompaction).
// Assumes: the caller owns and tracks Key and Meta's compaction keys (mvcc's footprint), holds the
// delete right (beDel); every key of Key below end is to be deleted; batch > 0; fin is
// "finishedCompactRev".
// Specs: LockForSafeRangeDelete.spec, LockOutsideApply.spec, batchTxBuffered.UnsafeRange.spec
// (btRange: the first batch keys in order; the bytes lent while the session lives),
// UnsafeDelete.spec (beDelHeld), UnsafePut.spec, Unlock.spec (Sess.mid with the put and not the
// deletes, then Sess.fin at the commit), UnlockForSafeRangeDelete.spec, ForceCommit.spec,
// readTx.UnsafeRange.spec.
func ReqCompactionBatch(be backend.Backend, start, end, fin, rev []byte, batch int64) {
	be.LockForSafeRangeDelete()
	defer be.UnlockForSafeRangeDelete()
	for {
		tx := be.BatchTx()
		tx.LockOutsideApply()
		keys, _ := tx.UnsafeRange(schema.Key, start, end, batch)
		for i := range keys {
			tx.UnsafeDelete(schema.Key, keys[i])
		}
		if int64(len(keys)) < batch {
			tx.UnsafePut(schema.Meta, fin, rev)
			tx.Unlock()
			break
		}
		tx.Unlock()
		be.ForceCommit()
	}
	rt := be.ReadTx()
	rt.RLock()
	ks, _ := rt.UnsafeRange(schema.Key, start, end, 0)
	_, vs := rt.UnsafeRange(schema.Meta, fin, nil, 0)
	rt.RUnlock()
	if len(ks) != 0 || len(vs) != 1 || !bytes.Equal(vs[0], rev) {
		panic("compaction-batch: a deleted key is still read, or the finished key is missing")
	}
}

// REQ backend/post-lock-hook: a post-lock hook set on the backend runs under every
// LockInsideApply, holding the lock, and may read the shared read transaction without RLock.
// Users: server/etcdserver/server.go:409, 1098 (SetTxPostLockInsideApplyHook), :2478-2484 (the hook:
// UnsafeConsistentIndex reads cindex.go:102-110 on a fresh member), every LockInsideApply.
// Assumes: the caller holds the hook's whole share; the Meta key k is tracked by the caller.
// Specs: backend.SetTxPostLockInsideApplyHook.spec, LockInsideApply.spec (hookRun with the
// session: beSess_rd), readTx.UnsafeRange.spec, Unlock.spec.
func ReqPostLockHook(be backend.Backend, k []byte) {
	ran := false
	be.SetTxPostLockInsideApplyHook(func() {
		_, _ = be.ReadTx().UnsafeRange(schema.Meta, k, nil, 0)
		ran = true
	})
	tx := be.BatchTx()
	tx.LockInsideApply()
	tx.Unlock()
	if !ran {
		panic("post-lock-hook: the hook did not run under the lock")
	}
}

// REQ backend/maintenance: Defrag, Hash and the size reads return (no panic); the sizes may be read
// after the backend's close (the quota's and bootstrap's readers).
// Users: server/etcdserver/server.go:976 (Defragment), bootstrap.go:323, storage/mvcc/kvstore.go:161
// (Hash), storage/quota.go:133, bootstrap.go:284 (Size, SizeInUse).
// Assumes: an open share for Defrag; a reader slot for Hash; the caller holds every tracker to
// close (the hooks' cells untracked).
// Specs: backend.Defrag.spec, backend.Hash.spec (ignOk of nil), backend.Close.spec,
// backend.Size.spec, backend.SizeInUse.spec.
func ReqMaintenance(be backend.Backend) {
	_ = be.Defrag()
	_, _ = be.Hash(nil)
	be.Close()
	_, _ = be.Size(), be.SizeInUse()
}

// REQ backend/open-snapshot-file: a backend opened over a received snapshot's database file reads
// what the snapshot's backend had committed.
// Users: server/storage/backend.go:61-70 (OpenSnapshotBackend: the snap dir's file renamed over the
// backend's path, then OpenBackend).
// Assumes: the file at path is the bytes of a snapshot of an image holding k = v (beFile_of from
// 4c's fileHolds_image); a reader slot.
// Specs: New.spec (beFile), Durable.beFile_of, readTx.RLock.spec, readTx.UnsafeRange.spec.
func ReqOpenSnapshotFile(lg *zap.Logger, path string, k, v []byte) {
	be := openBackend(lg, path, nil)
	rt := be.ReadTx()
	rt.RLock()
	_, vs := rt.UnsafeRange(schema.Alarm, k, nil, 0)
	rt.RUnlock()
	if len(vs) != 1 || !bytes.Equal(vs[0], v) {
		panic("open-snapshot-file: the opened backend lost the snapshot's entry")
	}
}
