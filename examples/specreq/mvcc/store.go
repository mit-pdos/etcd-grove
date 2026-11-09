// Requirement snippets for mvcc's store and its transactions (batch 3e).
//
// The store's users: the server's request path and apply thread through etcd's txn package
// (server/etcdserver/txn), the apply's compaction (server/etcdserver/apply/backend.go), the
// server's snapshot (server.go, snapshot_merge.go), the lessor's range deleter (lease/lessor.go),
// the v3rpc header (api/v3rpc/header.go), and the randomized tester (examples/mvccrand).
package mvcc

import (
	"bytes"
	"context"
	"errors"

	"go.etcd.io/etcd/pkg/v3/traceutil"
	"go.etcd.io/etcd/server/v3/lease"
	smvcc "go.etcd.io/etcd/server/v3/storage/mvcc"
)

// REQ mvcc/read-floor: a read transaction begun after the store reached revision floor reads at
// floor or later, and every key-value it returns is at or below its revision.
// Users: server/etcdserver/txn/range.go:53 (a linearizable Range after the applied index reached
// the read index), examples/mvccrand/mvccrand.go:636 (readers after the writer's published rev).
// Assumes: the store reached floor before this call (the client's invariant: the writer published
// it after its End); the store is never restored below it.
// Specs: store.Read.spec (KV.Read.contract: the update fires at the current state, whose revision
// the caller's invariant bounds below), metricsTxnWrite.Rev/Range/End.spec; laws:
// mvccState_reachable.
func ReqReadFloor(kv smvcc.KV, floor int64, key []byte) {
	tr := kv.Read(smvcc.ConcurrentReadTxMode, traceutil.TODO())
	defer tr.End()
	if tr.Rev() < floor {
		panic("read-floor: a read below a revision the store reached")
	}
	res, err := tr.Range(context.TODO(), key, nil, smvcc.RangeOptions{})
	if err != nil {
		panic("read-floor: a read at the current revision failed")
	}
	if res.Rev != tr.Rev() {
		panic("read-floor: the result's revision is not the transaction's")
	}
	for _, kv := range res.KVs {
		if kv.ModRevision > res.Rev || kv.ModRevision <= 0 || kv.CreateRevision <= 0 ||
			kv.Version <= 0 {
			panic("read-floor: a key-value out of the transaction's history")
		}
	}
}

// REQ mvcc/sole-writer: the only writer of the store knows the state its transaction begins at:
// its revision, a put's revision (one more), its own writes visible to its reads, and the
// revision after End.
// Users: server/etcdserver/txn/put.go:30, txn.go:32 (the apply thread is the store's sole writer;
// txn reads the key's previous value inside its write transaction), examples/mvccrand/mvccrand.go:430.
// Assumes: no other goroutine writes, compacts or restores the store (the caller's invariant holds
// the store's state); key is not empty; no lease (lease 0).
// Specs: store.Write.spec, metricsTxnWrite.{Rev,Put,Range,End}.spec (Txn.End's two updates fired
// at the writer's own state), store.Read.spec.
func ReqSoleWriter(kv smvcc.KV, key, val []byte) {
	tr := kv.Read(smvcc.ConcurrentReadTxMode, traceutil.TODO())
	rev0 := tr.Rev()
	tr.End()

	tw := kv.Write(traceutil.TODO())
	if tw.Rev() != rev0 {
		panic("sole-writer: the write transaction is not at the writer's revision")
	}
	if tw.Put(key, val, lease.NoLease) != rev0+1 {
		panic("sole-writer: a put's revision is not the next one")
	}
	res, err := tw.Range(context.TODO(), key, nil, smvcc.RangeOptions{})
	if err != nil || len(res.KVs) != 1 || !bytes.Equal(res.KVs[0].Value, val) ||
		res.KVs[0].ModRevision != rev0+1 || res.Rev != rev0+1 {
		panic("sole-writer: the transaction's read does not see its put")
	}
	if len(tw.Changes()) != 1 {
		panic("sole-writer: a put is not one change")
	}
	tw.End()

	tr = kv.Read(smvcc.ConcurrentReadTxMode, traceutil.TODO())
	defer tr.End()
	if tr.Rev() != rev0+1 {
		panic("sole-writer: the committed revision is not the transaction's")
	}
}

// REQ mvcc/delete-range: a range delete deletes exactly the range's present keys, at the pending
// revision; one of nothing writes no revision.
// Users: server/etcdserver/txn/delete.go:39 (deleteRange's n and the response's revision),
// lease/lessor.go:350 (Revoke's deletes), examples/mvccrand/mvccrand.go:445.
// Assumes: the sole writer (as sole-writer); key is present and alone in [key, end); absent is
// absent.
// Specs: store.Write.spec, metricsTxnWrite.{DeleteRange,End}.spec (Txn.DeleteRange: rangeKeys of the
// transaction's store).
func ReqDeleteRange(kv smvcc.KV, key, end, absent []byte) {
	tw := kv.Write(traceutil.TODO())
	rev0 := tw.Rev()
	if n, rev := tw.DeleteRange(absent, nil); n != 0 || rev != rev0 {
		panic("delete-range: a delete of nothing wrote a revision")
	}
	if n, rev := tw.DeleteRange(key, end); n != 1 || rev != rev0+1 {
		panic("delete-range: not exactly the range's key, at the next revision")
	}
	res, err := tw.Range(context.TODO(), key, end, smvcc.RangeOptions{CountOnly: true})
	if err != nil || res.Count != 0 {
		panic("delete-range: a deleted key is still there")
	}
	tw.End()
}

// REQ mvcc/read-only-txn: a read transaction made a write transaction (txn's read-only path)
// reads the same, has no changes, and ends as the read transaction.
// Users: server/etcdserver/txn/txn.go:69, examples/mvccrand/mvccrand.go:475.
// Assumes: nothing.
// Specs: store.Read.spec, NewReadOnlyTxnWrite.spec, txnReadWrite.{Rev,Range,Changes,End}.spec.
func ReqReadOnlyTxn(kv smvcc.KV, key []byte) {
	tr := kv.Read(smvcc.SharedBufReadTxMode, traceutil.TODO())
	rev := tr.Rev()
	tw := smvcc.NewReadOnlyTxnWrite(tr)
	if tw.Rev() != rev || len(tw.Changes()) != 0 {
		panic("read-only-txn: not the read transaction")
	}
	if _, err := tw.Range(context.TODO(), key, nil, smvcc.RangeOptions{}); err != nil {
		panic("read-only-txn: a read at the current revision failed")
	}
	tw.End()
}

// REQ mvcc/range-errors: a read past the current revision fails with ErrFutureRev (with the
// current revision), one below the compaction revision with ErrCompacted; a count-only read
// counts; a keys-only read reports lease 0 and no value; a limit cuts the key-values, not a total
// count.
// Users: server/etcdserver/txn/range.go:59-108 (executeRange: the options it passes, its error
// mapping), txn/range.go:174 (checkRange's own check against FirstRev), examples/mvccrand/mvccrand.go:223.
// Assumes: cur is the store's revision, crev its compaction revision (≥ 1) and no write or
// compaction happens meanwhile (the caller's invariant); [key, end) holds at least two keys at cur.
// Specs: store.Range.spec (KV.Range.contract: rangeOut), init (the error variables).
func ReqRangeErrors(kv smvcc.KV, cur, crev int64, key, end []byte) {
	ctx := context.TODO()
	r, err := kv.Range(ctx, key, end, smvcc.RangeOptions{Rev: cur + 1})
	if !errors.Is(err, smvcc.ErrFutureRev) || r.Rev != cur {
		panic("range-errors: a future read did not fail with ErrFutureRev")
	}
	if crev > 1 {
		if _, err := kv.Range(ctx, key, end, smvcc.RangeOptions{Rev: crev - 1}); !errors.Is(err, smvcc.ErrCompacted) {
			panic("range-errors: a compacted read did not fail with ErrCompacted")
		}
	}
	all, err := kv.Range(ctx, key, end, smvcc.RangeOptions{CountOnly: true})
	if err != nil || len(all.KVs) != 0 || all.Count < 2 {
		panic("range-errors: a count-only read")
	}
	ko, err := kv.Range(ctx, key, end, smvcc.RangeOptions{FastKeysOnly: true, Limit: 1, WithTotalCount: true})
	if err != nil || len(ko.KVs) != 1 || ko.KVs[0].Lease != 0 || len(ko.KVs[0].Value) != 0 ||
		ko.Count != all.Count {
		panic("range-errors: a keys-only read with a limit and a total count")
	}
	lim, err := kv.Range(ctx, key, end, smvcc.RangeOptions{Limit: 1})
	if err != nil || len(lim.KVs) != 1 || lim.Count != 1 {
		panic("range-errors: a limited read without a total count")
	}
}

// REQ mvcc/views: the store's own Rev, FirstRev and Range (one-shot read transactions) and its
// Put (a one-shot write transaction).
// Users: server/etcdserver/v3_server.go:429, 730, api/v3rpc/header.go:35 (s.KV().Rev() for headers),
// apply/backend.go:78 (the compaction's header: Range of "compaction"), the v3compactor's
// RevGetter (api/v3compactor/revision.go: Rev()).
// Assumes: the caller is the sole writer (for the put's revision); no lease.
// Specs: store.{Rev,FirstRev,Range,Put}.spec (promoted from the read and write views).
func ReqViews(kv smvcc.KV, key, val []byte) {
	rev := kv.Rev()
	if kv.FirstRev() > rev {
		panic("views: the compaction revision is past the current one")
	}
	rr, err := kv.Range(context.TODO(), []byte("compaction"), nil, smvcc.RangeOptions{})
	if err != nil || rr.Rev != rev {
		panic("views: a read at the current revision")
	}
	if kv.Put(key, val, lease.NoLease) != rev+1 {
		panic("views: a put's revision is not the next one")
	}
}

// REQ mvcc/commit: a forced commit does not panic, at any time (the server's snapshot commits
// before reading the backend).
// Users: server/etcdserver/snapshot_merge.go:36, server.go:2129, examples/mvccrand.
// Assumes: nothing.
// Specs: store.Commit.spec (storageReq: the client's commit request).
func ReqCommit(kv smvcc.KV) {
	kv.Commit()
}
