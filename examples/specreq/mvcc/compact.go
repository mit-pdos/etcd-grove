package mvcc

import (
	"bytes"
	"context"
	"errors"

	"go.etcd.io/etcd/pkg/v3/traceutil"
	"go.etcd.io/etcd/server/v3/storage/backend"
	smvcc "go.etcd.io/etcd/server/v3/storage/mvcc"
	"go.etcd.io/etcd/server/v3/storage/schema"
)

// REQ mvcc/compact: a compaction at a revision above the compaction revision and at most the
// current one succeeds; afterwards reads report it as the first revision, a read below it fails
// with ErrCompacted, at it succeeds; waiting on the channel (a physical compaction) does not panic.
// Users: server/etcdserver/apply/backend.go:66-80 (applierV3backend.Compaction: Compact, then the
// header's revision by a Range), apply/uber_applier.go:97 (ErrCompacted is a success),
// server/etcdserver/v3_server.go (Compact's physical wait on the channel), examples/etcd/putgetc's
// auto-compactor.
// Assumes: reader tokens for the reads; context.TODO() is never done (Context's laws); the caller
// holds the store's open token (compactions are not concurrent: etcd compacts
// from its apply thread); crev < rev ≤ cur where crev, cur are the store's (the caller's invariant
// holds the state); rev ≠ 0 (W0's scope).
// Specs: store.Compact.spec (KV.Compact.contract: the hook and the commit, compactChanOk),
// store.FirstRev.spec, store.Range.spec.
func ReqCompact(kv smvcc.KV, rev int64, key []byte) {
	ch, err := kv.Compact(traceutil.TODO(), rev)
	if err != nil {
		panic("compact: a compaction in range failed")
	}
	<-ch
	if kv.FirstRev() != rev {
		panic("compact: the first revision is not the compaction's")
	}
	if rev > 1 {
		if _, err := kv.Range(context.TODO(), key, nil, smvcc.RangeOptions{Rev: rev - 1}); !errors.Is(err, smvcc.ErrCompacted) {
			panic("compact: a read below the compaction did not fail")
		}
	}
	if _, err := kv.Range(context.TODO(), key, nil, smvcc.RangeOptions{Rev: rev}); err != nil {
		panic("compact: a read at the compaction revision failed")
	}
}

// REQ mvcc/compact-errors: a compaction at or below the compaction revision fails with
// ErrCompacted (and a channel the caller may wait on), one past the current revision with
// ErrFutureRev and no channel; neither changes the store.
// Users: apply/uber_applier.go:97, api/v3compactor/{periodic,revision}.go (errors.Is(err,
// mvcc.ErrCompacted)), server/etcdserver/v3_server.go (the server's Compact returns the error).
// Assumes: the open token; the store's compaction revision crev ≥ 1 and current revision cur, no
// write meanwhile.
// Specs: store.Compact.spec (its error arms), init.
func ReqCompactErrors(kv smvcc.KV, crev, cur int64) {
	ch, err := kv.Compact(traceutil.TODO(), crev)
	if !errors.Is(err, smvcc.ErrCompacted) || ch == nil {
		panic("compact-errors: a compaction at the compaction revision")
	}
	<-ch // closed once the compactions before it ran (or never: a stopped store; no panic)
	ch, err = kv.Compact(traceutil.TODO(), cur+1)
	if !errors.Is(err, smvcc.ErrFutureRev) || ch != nil {
		panic("compact-errors: a compaction past the current revision")
	}
	if kv.FirstRev() != crev || kv.Rev() != cur {
		panic("compact-errors: a failed compaction changed the store")
	}
}

// REQ mvcc/compact-delete-returned: within one batch session under the safe-range lock, the
// compaction deletes keys its own UnsafeRange returned, passing the returned byte slices themselves
// (the storage's memory, lent against the session's liveness), and reads the later returned keys
// and every returned value after those deletes: a delete changes none of the returned bytes; a
// range of the batch afterwards no longer has the deleted keys.
// Users: server/storage/mvcc/kvstore_compaction.go:31-71 (scheduleCompaction: UnsafeRange, then
// UnsafeDelete(schema.Key, keys[i]) and h.WriteKeyValue(keys[i], values[i]) for each).
// Assumes: be is etcd's backend opened for mvcc (keyBackend_intro, Key made); the caller holds the
// delete right (kbSafe: compactions one at a time) and an open share; nothing in [start, end) was
// put by this session (the batch begins here); start < end, end non-empty.
// Specs: keyBackend's rows LockForSafeRangeDelete, BatchTx, LockOutsideApply, UnsafeRange
// (rangeLent against kbLive's share), UnsafeDelete (D.keys k = D0.keys k; the key's bytes given
// back), Unlock, UnlockForSafeRangeDelete; kbLive_fractional; bbolt's txLive/txBytes_acc (A11 S1)
// through 4a.
func ReqCompactDeleteReturned(be backend.Backend, start, end []byte) {
	be.LockForSafeRangeDelete()
	defer be.UnlockForSafeRangeDelete()
	tx := be.BatchTx()
	tx.LockOutsideApply()
	keys, values := tx.UnsafeRange(schema.Key, start, end, 1000)
	ks := make([][]byte, len(keys))
	vs := make([][]byte, len(values))
	for i := range keys {
		ks[i] = append([]byte(nil), keys[i]...)
		vs[i] = append([]byte(nil), values[i]...)
	}
	for i := range keys {
		tx.UnsafeDelete(schema.Key, keys[i])
		for j := range keys {
			if !bytes.Equal(keys[j], ks[j]) || !bytes.Equal(values[j], vs[j]) {
				panic("compact-delete-returned: a delete changed a returned key or value")
			}
		}
	}
	left, _ := tx.UnsafeRange(schema.Key, start, end, 1000)
	for _, k := range left {
		for _, d := range ks {
			if bytes.Equal(k, d) {
				panic("compact-delete-returned: a deleted key is still in the batch")
			}
		}
	}
	tx.Unlock()
}
