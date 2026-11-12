package backend

import (
	"go.etcd.io/etcd/server/v3/storage/schema"
)

// REQ backend/session-atomic: a concurrent read transaction sees the puts of one batch session all
// together or none of them.
// Users: storage/mvcc/kvstore_txn.go:177-216 (a write transaction's puts, one session), :55 and
// :126 (a read transaction: ConcurrentReadTx, one key at a time).
func ReqSessionAtomic() {
	be := openWith("specreq-backend-atomic.db", schema.Key)
	done := make(chan struct{})
	go func() {
		for i := byte(1); i <= 3; i++ {
			rt := be.ConcurrentReadTx()
			rt.RLock()
			a, _ := rt.UnsafeRange(schema.Key, []byte{i, 0}, nil, 0)
			b, _ := rt.UnsafeRange(schema.Key, []byte{i, 1}, nil, 0)
			rt.RUnlock()
			if len(a) != len(b) {
				panic("session-atomic: a read saw part of a session's puts")
			}
		}
		close(done)
	}()
	tx := be.BatchTx()
	for i := byte(1); i <= 3; i++ {
		tx.LockInsideApply()
		tx.UnsafeSeqPut(schema.Key, []byte{i, 0}, []byte("v"))
		tx.UnsafeSeqPut(schema.Key, []byte{i, 1}, []byte("v"))
		tx.Unlock()
	}
	<-done
	be.Close()
}

// REQ backend/last-write-wins: a read returns a key's last put: over a put of the same session, of
// an earlier one, and (buffered) over a committed one; through the shared ReadTx and the batch.
// Users: storage/schema/cindex.go:89 (the consistent index put at every apply, and at every commit
// through storage/hooks.go:46), read back by cindex.go:55 (ReadTx) and :39 (the batch).
func ReqLastWriteWins() {
	be := openWith("specreq-backend-lww.db", schema.Meta)
	tx := be.BatchTx()
	tx.LockOutsideApply()
	tx.UnsafePut(schema.Meta, []byte("k"), []byte("1"))
	tx.UnsafePut(schema.Meta, []byte("k"), []byte("2"))
	tx.Unlock()
	ok := get(be.ReadTx(), schema.Meta, "k") == "2" && getBatch(be, schema.Meta, "k") == "2"
	be.ForceCommit()
	put(be, schema.Meta, "k", "3")
	if !ok || get(be.ReadTx(), schema.Meta, "k") != "3" || getBatch(be, schema.Meta, "k") != "3" {
		panic("last-write-wins: a read missed the last put")
	}
	be.Close()
}

// REQ backend/maintenance: Defrag (also one that fails) changes nothing a read returns, and Hash
// may be called (it returns a value for the caller to report).
// Users: etcdserver/server.go:976 (the Defragment RPC; the server serves on from the same backend),
// etcdserver/bootstrap.go:323 (on boot), storage/mvcc/kvstore.go:160-161 (the Hash RPC's hash:
// ForceCommit, then Hash with schema.DefaultIgnores; nothing in etcd compares it).
func ReqMaintenance() {
	be := openWith("specreq-backend-maint.db", schema.Alarm)
	put(be, schema.Alarm, "a", "1")
	put(be, schema.Alarm, "b", "2")
	tx := be.BatchTx()
	tx.LockOutsideApply()
	tx.UnsafeDelete(schema.Alarm, []byte("b"))
	tx.Unlock()
	be.ForceCommit()
	_, _ = be.Hash(schema.DefaultIgnores)
	_ = be.Defrag()
	if get(be.ReadTx(), schema.Alarm, "a") != "1" || get(be.ReadTx(), schema.Alarm, "b") != "" {
		panic("maintenance: Defrag changed the content")
	}
	be.Close()
}
