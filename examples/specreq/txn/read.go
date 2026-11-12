// Package txn holds the requirement snippets of etcd's server transactions (batch 3b,
// SpecPlan/Spec/go_etcd_io/etcd/server/v3/etcdserver/txn/): minimal uses of Range, Count, Put, DeleteRange
// and Txn in the patterns their users rely on (the request path's reads, v3_server.go; the apply
// thread's writes, apply/backend.go), each reliance an explicit panic.
//
// Common assumptions (the proofs' setting): kv is a member's mvcc store and le its lessor (mvccKV,
// Lease.isLessor, mvccLessor); the caller owns the store's state (mvccState) in an invariant of its own and fires
// the updates; requests are what the gRPC layer passes on (checkRangeRequest: a key, a valid sort;
// checkTxnRequest and checkIntervals: txnSafe); an empty RangeEnd is nil (as protobuf decodes it).
// The write snippets (write.go) run on the apply thread: the store's only writer, its lessor's
// grants and revocations its own (the writer token Lease.lessorState, with the store and lessor
// attached), with context.TODO().
package txn

import (
	"context"
	"errors"

	"go.uber.org/zap"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/server/v3/etcdserver/txn"
	"go.etcd.io/etcd/server/v3/lease"
	"go.etcd.io/etcd/server/v3/storage/mvcc"
)

// REQ txn/range-limit-count: a limited range returns at most the limit, with the total count, and
// More exactly when it cut.
// Users: v3_server.go:149 (EtcdServer.Range, withTotalCount true); apply/backend.go:59.
// Assumes: none beyond the common ones (any concurrent writer: the answer is of one state).
// Specs: Range.spec; laws: rangeOut's definition (count-only false, default order).
func ReqRangeLimitCount(ctx context.Context, lg *zap.Logger, kv mvcc.KV, k, end []byte) {
	resp, _, err := txn.Range(ctx, lg, kv, &pb.RangeRequest{Key: k, RangeEnd: end, Limit: 1}, true)
	if err != nil {
		return // the context's error
	}
	if len(resp.Kvs) > 1 {
		panic("range-limit-count: over the limit")
	}
	if resp.More != (resp.Count > 1) {
		panic("range-limit-count: More is not whether it cut")
	}
	if resp.Count > 0 && len(resp.Kvs) != 1 {
		panic("range-limit-count: a key missing")
	}
}

// REQ txn/range-pinned-rev: a range at a pinned revision answers at it, or fails with mvcc's
// ErrCompacted (below the compaction) or ErrFutureRev (above the store's revision); the header is
// the store's revision, at least the pinned one.
// Users: v3_server.go:223 (rangeStream pins the first page's revision), the client's WithRev gets.
// Assumes: rev > 0.
// Specs: Range.spec (errIs: the sentinels' globals, so errors.Is evaluates); laws: errIs_agree,
// W0's revErr; 3e's Mvcc.mvccState_reachable (a record of storeAt rev has modRev <= rev).
func ReqRangePinnedRev(ctx context.Context, lg *zap.Logger, kv mvcc.KV, k []byte, rev int64) {
	resp, _, err := txn.Range(ctx, lg, kv, &pb.RangeRequest{Key: k, Revision: rev}, true)
	if errors.Is(err, mvcc.ErrCompacted) || errors.Is(err, mvcc.ErrFutureRev) {
		if resp != nil {
			panic("range-pinned-rev: a reply with a revision error")
		}
		return
	}
	if err != nil {
		return // the context's error
	}
	if resp.Header.Revision < rev {
		panic("range-pinned-rev: answered below the pinned revision")
	}
	for _, kv := range resp.Kvs {
		if kv.ModRevision > rev {
			panic("range-pinned-rev: a key-value written after the pinned revision")
		}
	}
}

// REQ txn/range-stream-pages: rangeStream's paging: a page of at most the limit, More when it cut,
// the next page from after the last key, the rest counted at the same revision; the pages never
// overlap.
// Users: v3_server.go:223-255 (rangeStream, withTotalCount false, then Count).
// Assumes: rev is a revision of the store at least its compaction (the first page's header).
// Specs: Range.spec, Count.spec.
func ReqRangeStreamPages(ctx context.Context, lg *zap.Logger, kv mvcc.KV, k, end []byte, rev int64) {
	r := &pb.RangeRequest{Key: k, RangeEnd: end, Revision: rev, Limit: 2}
	resp, _, err := txn.Range(ctx, lg, kv, r, false)
	if err != nil {
		return
	}
	if len(resp.Kvs) > 2 || (resp.More && len(resp.Kvs) != 2) {
		panic("range-stream-pages: a page not cut at its limit")
	}
	if !resp.More {
		return
	}
	next := append(append([]byte{}, resp.Kvs[len(resp.Kvs)-1].Key...), 0)
	rest, err := txn.Count(ctx, lg, kv, next, end, rev)
	if err != nil {
		return
	}
	if rest < 1 {
		panic("range-stream-pages: More, but nothing after the page")
	}
	r2 := &pb.RangeRequest{Key: next, RangeEnd: end, Revision: rev, Limit: 2}
	resp2, _, err := txn.Range(ctx, lg, kv, r2, false)
	if err != nil {
		return
	}
	for _, kv2 := range resp2.Kvs {
		for _, kv1 := range resp.Kvs {
			if string(kv1.Key) >= string(kv2.Key) {
				panic("range-stream-pages: pages overlap")
			}
		}
	}
}

// REQ txn/count-only: a count-only range has no key-values, and Count is the count.
// Users: v3_server.go:199 (rangeStream's count-only branch), :255 (Count).
// Assumes: none.
// Specs: Range.spec, Count.spec.
func ReqCountOnly(ctx context.Context, lg *zap.Logger, kv mvcc.KV, k, end []byte) {
	resp, _, err := txn.Range(ctx, lg, kv, &pb.RangeRequest{Key: k, RangeEnd: end, CountOnly: true}, false)
	if err != nil {
		return
	}
	if len(resp.Kvs) != 0 || resp.More {
		panic("count-only: key-values returned")
	}
	if resp.Count < 0 {
		panic("count-only: negative count")
	}
}

// REQ txn/txn-read-only: a read-only transaction's ranges are all answered at one revision, the
// header's, and it has one response per operation of the taken branch.
// Users: v3_server.go:366 (EtcdServer.Txn's read-only transactions, skip false).
// Assumes: none (le is unused by a read-only transaction).
// Specs: IsTxnReadonly.spec, Txn.spec; laws: runEvs_readonly.
func ReqTxnReadOnly(ctx context.Context, lg *zap.Logger, kv mvcc.KV, le lease.Lessor, a, b []byte) {
	rt := &pb.TxnRequest{Success: []*pb.RequestOp{
		{Request: &pb.RequestOp_RequestRange{RequestRange: &pb.RangeRequest{Key: a}}},
		{Request: &pb.RequestOp_RequestRange{RequestRange: &pb.RangeRequest{Key: b}}},
	}}
	if !txn.IsTxnReadonly(rt) {
		panic("txn-read-only: not read-only")
	}
	resp, _, err := txn.Txn(ctx, lg, rt, false, kv, le, false)
	if err != nil {
		return // the context's error
	}
	if !resp.Succeeded || len(resp.Responses) != 2 {
		panic("txn-read-only: wrong shape")
	}
	for _, ro := range resp.Responses {
		rr := ro.GetResponseRange()
		if rr == nil || rr.Header.Revision != resp.Header.Revision {
			panic("txn-read-only: a range at another revision")
		}
	}
}

// REQ txn/range-sorted-keys-only: a keys-only range sorted by descending mod revision with a filter
// returns the filtered keys in that order, with no value and lease 0 (the fast keys-only path:
// issues/etcd-range-keys-only-lease.md), at most the limit.
// Users: v3_server.go:149 (etcdctl get --prefix --keys-only --sort-by=MODIFY --order=DESCEND, a
// client's WithSort/WithMinModRev); the answer 2c's read registry and 3a's kvStep rely on.
// Assumes: none.
// Specs: Range.spec (rangeOut: the fast path's value and lease cleared before the sort);
// laws: goSort_sorted, rangeOut_answers.
func ReqRangeSortedKeysOnly(ctx context.Context, lg *zap.Logger, kv mvcc.KV, k, end []byte, minMod int64) {
	r := &pb.RangeRequest{Key: k, RangeEnd: end, KeysOnly: true, Limit: 3, MinModRevision: minMod,
		SortTarget: pb.RangeRequest_MOD, SortOrder: pb.RangeRequest_DESCEND}
	resp, _, err := txn.Range(ctx, lg, kv, r, true)
	if err != nil {
		return
	}
	if len(resp.Kvs) > 3 {
		panic("range-sorted-keys-only: over the limit")
	}
	for i, x := range resp.Kvs {
		if len(x.Value) != 0 || x.Lease != 0 {
			panic("range-sorted-keys-only: a value or a lease")
		}
		if x.ModRevision < minMod {
			panic("range-sorted-keys-only: the filter missed")
		}
		if i > 0 && resp.Kvs[i-1].ModRevision < x.ModRevision {
			panic("range-sorted-keys-only: out of order")
		}
	}
}
