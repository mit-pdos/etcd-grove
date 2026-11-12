package backend

import (
	"errors"

	"go.etcd.io/etcd/server/v3/storage/schema"
)

// REQ backend/foreach: a whole-bucket visit on the shared ReadTx visits each entry once, with its
// latest value, also for a key both committed and rewritten since; on the batch it visits them in
// key order; the visitor's error stops the visit and is returned.
// Users: storage/schema/alarm.go:84-100 (GetAllAlarms on the ReadTx; an unmarshal error returned),
// membership.go:95-98, auth_users.go:85-94, storage/schema/lease.go:31-40 (MustUnsafeGetAllLeases,
// an unmarshal error returned) under LockOutsideApply (lease/lessor.go:811-813).
func ReqForEach() {
	be := openWith("specreq-backend-foreach.db", schema.Alarm)
	put(be, schema.Alarm, "a", "1")
	put(be, schema.Alarm, "b", "1")
	be.ForceCommit()
	put(be, schema.Alarm, "a", "2")
	put(be, schema.Alarm, "c", "1")

	got := ""
	visit := func(k, v []byte) error { got += string(k) + string(v); return nil }
	rt := be.ReadTx()
	rt.RLock()
	err := rt.UnsafeForEach(schema.Alarm, visit)
	n, stop := 0, errors.New("stop")
	err2 := rt.UnsafeForEach(schema.Alarm, func(k, v []byte) error { n++; return stop })
	rt.RUnlock()
	if err != nil || len(got) != 6 || !contains(got, "a2", "b1", "c1") {
		panic("foreach: the read transaction's visit is not each entry once, with its value")
	}
	if err2 != stop || n != 1 {
		panic("foreach: the visitor's error did not stop the visit, or was not returned")
	}

	got = ""
	tx := be.BatchTx()
	tx.LockOutsideApply()
	err = tx.UnsafeForEach(schema.Alarm, visit)
	tx.Unlock()
	if err != nil || got != "a2b1c1" {
		panic("foreach: the batch's visit is not every entry in key order")
	}
	be.Close()
}

// contains says whether s, a sequence of two-byte entries, holds each of es.
func contains(s string, es ...string) bool {
	for _, e := range es {
		found := false
		for i := 0; i+2 <= len(s); i += 2 {
			found = found || s[i:i+2] == e
		}
		if !found {
			return false
		}
	}
	return true
}

// REQ backend/compaction-batch: under the safe-range lock, batches of a limited range of a
// safe-range bucket, each deleting what its range returned and committed, the last also putting
// the finished-compaction key; after the last Unlock the deleted keys are gone and the key is set.
// Users: storage/mvcc/kvstore_compaction.go:28-95 (scheduleCompaction).
func ReqCompactionBatch() {
	be := openWith("specreq-backend-compaction.db", schema.Key, schema.Meta)
	tx := be.BatchTx()
	tx.LockOutsideApply()
	for _, k := range []string{"a", "b", "c"} {
		tx.UnsafeSeqPut(schema.Key, []byte(k), []byte("v"))
	}
	tx.Unlock()

	be.LockForSafeRangeDelete()
	for {
		tx.LockOutsideApply()
		keys, _ := tx.UnsafeRange(schema.Key, []byte("a"), []byte("z"), 2)
		for _, k := range keys {
			tx.UnsafeDelete(schema.Key, k)
		}
		if len(keys) < 2 {
			tx.UnsafePut(schema.Meta, schema.FinishedCompactKeyName, []byte("rev"))
			tx.Unlock()
			break
		}
		tx.Unlock()
		be.ForceCommit()
	}
	be.UnlockForSafeRangeDelete()

	rt := be.ReadTx()
	rt.RLock()
	ks, _ := rt.UnsafeRange(schema.Key, []byte("a"), []byte("z"), 0)
	rt.RUnlock()
	if len(ks) != 0 || get(rt, schema.Meta, string(schema.FinishedCompactKeyName)) != "rev" {
		panic("compaction-batch: a deleted key is still read, or the finished key is missing")
	}
	be.Close()
}

// REQ backend/post-lock-hook: a post-lock hook set on the backend runs under every
// LockInsideApply, holding the lock, and may read the shared ReadTx without RLock.
// Users: etcdserver/server.go:409, :1098 (SetTxPostLockInsideApplyHook), :2478-2484 (the hook:
// UnsafeConsistentIndex, etcdserver/cindex/cindex.go:102-110, reads the ReadTx on a fresh member),
// every LockInsideApply.
func ReqPostLockHook() {
	be := openWith("specreq-backend-post-lock.db", schema.Meta)
	put(be, schema.Meta, "k", "v")
	got := ""
	be.SetTxPostLockInsideApplyHook(func() {
		_, vs := be.ReadTx().UnsafeRange(schema.Meta, []byte("k"), nil, 0)
		got = value(vs)
	})
	be.BatchTx().LockInsideApply()
	be.BatchTx().Unlock()
	if got != "v" {
		panic("post-lock-hook: the hook did not run under the lock, or misread the ReadTx")
	}
	be.Close()
}

// REQ backend/seq-range: in a safe-range bucket written in increasing key order, a
// ConcurrentReadTx finds each key written; the shared ReadTx's unlimited range returns the range
// in key order, and, just after a commit (nothing buffered), a limited range its first entries.
// Users: storage/mvcc/kvstore_txn.go:259 (UnsafeSeqPut of increasing revisions), :55-60, :126
// (Read: a ConcurrentReadTx, RLock, one revision at a time), storage/mvcc/kvstore.go:125-129,
// :327-358 (NewStore's ForceCommit, then restore's ranges of Key in chunks of restoreChunkKeys).
func ReqSeqRange() {
	be := openWith("specreq-backend-seq-range.db", schema.Key)
	tx := be.BatchTx()
	tx.LockInsideApply()
	tx.UnsafeSeqPut(schema.Key, []byte("a"), []byte("1"))
	tx.UnsafeSeqPut(schema.Key, []byte("b"), []byte("2"))
	tx.Unlock()
	crt := be.ConcurrentReadTx()
	crt.RLock()
	_, va := crt.UnsafeRange(schema.Key, []byte("a"), nil, 0)
	_, vb := crt.UnsafeRange(schema.Key, []byte("b"), nil, 0)
	crt.RUnlock()
	if value(va) != "1" || value(vb) != "2" {
		panic("seq-range: a concurrent read missed a written key")
	}

	rt := be.ReadTx()
	rt.RLock()
	ks, _ := rt.UnsafeRange(schema.Key, []byte("a"), []byte("c"), 0)
	rt.RUnlock()
	if len(ks) != 2 || string(ks[0]) != "a" || string(ks[1]) != "b" {
		panic("seq-range: an unlimited range is not the range in key order")
	}
	be.ForceCommit()
	rt.RLock()
	ks, _ = rt.UnsafeRange(schema.Key, []byte("a"), []byte("c"), 1)
	rt.RUnlock()
	if len(ks) != 1 || string(ks[0]) != "a" {
		panic("seq-range: a limited range just after a commit is not its first entry")
	}
	be.Close()
}
