package backend

import (
	"bytes"

	"go.etcd.io/etcd/server/v3/storage/backend"
	"go.etcd.io/etcd/server/v3/storage/schema"
)

// REQ backend/seq-range: in a safe-range bucket written in increasing key order, a concurrent read
// finds each key written, the shared read transaction's unlimited range returns the range in key
// order, and a limited one, when nothing of the bucket is buffered (just after a commit), its
// first entries.
// Users: storage/mvcc/kvstore_txn.go:259 (UnsafeSeqPut of increasing revisions), :126 (rangeKeys:
// one revision at a time on a ConcurrentReadTx), storage/mvcc/kvstore.go:327-355 (restore: ReadTx
// ranges of Key in chunks of restoreChunkKeys, after NewStore's ForceCommit).
// Assumes: the caller owns the Key bucket (published, its buffer flag tracked), a and b are above
// every key in it, a < b; a reader slot.
// Specs: UnsafeSeqPut.spec (Sess.fresh), Unlock.spec, backend.ConcurrentReadTx.spec (Key disjoint
// from the hooks' cells), concurrentReadTx.UnsafeRange.spec (lingerSingle: a key of the view is
// read exactly), backend.ForceCommit.spec (beReq: the step records the bucket clean,
// beCurIs_flush), readTx.UnsafeRange.spec (rdRange: no limit, the range in order; clean, the plain
// cut range).
func ReqSeqRange(be backend.Backend, a, b, va, vb, end []byte) {
	tx := be.BatchTx()
	tx.LockInsideApply()
	tx.UnsafeSeqPut(schema.Key, a, va)
	tx.UnsafeSeqPut(schema.Key, b, vb)
	tx.Unlock()

	rt := be.ConcurrentReadTx()
	ka, _ := rt.UnsafeRange(schema.Key, a, nil, 0)
	kb, _ := rt.UnsafeRange(schema.Key, b, nil, 0)
	rt.RUnlock()
	if len(ka) != 1 || len(kb) != 1 {
		panic("seq-range: a concurrent read missed a written key")
	}

	srt := be.ReadTx()
	srt.RLock()
	ks, _ := srt.UnsafeRange(schema.Key, a, end, 0)
	srt.RUnlock()
	if len(ks) != 2 || !bytes.Equal(ks[0], a) || !bytes.Equal(ks[1], b) {
		panic("seq-range: an unlimited range is not the range in key order")
	}

	be.ForceCommit()
	srt.RLock()
	ks, _ = srt.UnsafeRange(schema.Key, a, end, 1)
	srt.RUnlock()
	if len(ks) != 1 || !bytes.Equal(ks[0], a) {
		panic("seq-range: a limited range of a clean bucket is not its first entry")
	}
}

// REQ backend/meta-single: a non-safe-range bucket is read one key at a time (a nil end); the read
// finds the key whether it is buffered or committed, and never panics.
// Users: storage/schema/cindex.go (UnsafeReadConsistentIndex: Meta, nil end), storage/mvcc/
// store.go:28-34 (the compaction keys), storage/schema/version.go, auth's UnsafeGetUser.
// Assumes: the caller tracks the Meta key k; a reader slot.
// Specs: readTx.RLock.spec, readTx.UnsafeRange.spec (es = nil: limit 1; rdRange's single).
func ReqMetaSingle(be backend.Backend, k, v []byte) {
	tx := be.BatchTx()
	tx.LockOutsideApply()
	tx.UnsafePut(schema.Meta, k, v)
	tx.Unlock()
	rt := be.ReadTx()
	rt.RLock()
	_, vs := rt.UnsafeRange(schema.Meta, k, nil, 0)
	rt.RUnlock()
	if len(vs) != 1 || !bytes.Equal(vs[0], v) {
		panic("meta-single: a single-key read missed the buffered value")
	}
}
