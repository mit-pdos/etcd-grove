package txn

import (
	"bytes"
	"context"
	"errors"

	"go.uber.org/zap"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	srverrors "go.etcd.io/etcd/server/v3/etcdserver/errors"
	"go.etcd.io/etcd/server/v3/etcdserver/txn"
	"go.etcd.io/etcd/server/v3/lease"
	"go.etcd.io/etcd/server/v3/storage/mvcc"
)

// REQ txn/apply-put-then-range: the apply's put writes at the next revision, and a range after it
// sees the value at that mod revision.
// Users: apply/backend.go:51,59 (applierV3backend.Put then Range, as consecutive entries).
// Assumes: the sole writer (no other write between the calls).
// Specs: Put.spec, Range.spec; laws: putAns, putHist (W0's PutReq.record).
func ReqApplyPutThenRange(lg *zap.Logger, le lease.Lessor, kv mvcc.KV, k, v []byte) {
	presp, _, err := txn.Put(context.TODO(), lg, le, kv, &pb.PutRequest{Key: k, Value: v})
	if err != nil {
		panic("apply-put-then-range: a put without a lease or ignore flag failed")
	}
	rresp, _, err := txn.Range(context.TODO(), lg, kv, &pb.RangeRequest{Key: k}, true)
	if err != nil {
		panic("apply-put-then-range: a current range failed")
	}
	if len(rresp.Kvs) != 1 || !bytes.Equal(rresp.Kvs[0].Value, v) {
		panic("apply-put-then-range: lost write")
	}
	if rresp.Kvs[0].ModRevision != presp.Header.Revision || rresp.Header.Revision != presp.Header.Revision {
		panic("apply-put-then-range: wrong revision")
	}
}

// REQ txn/apply-put-ignore-value: a put with IgnoreValue of a missing key fails with
// ErrKeyNotFound and writes nothing; of a present key it keeps the value.
// Users: apply/backend.go:51 (a client's put WithIgnoreValue: clientv3 op.go).
// Assumes: the sole writer.
// Specs: Put.spec, Range.spec (errIs: ErrKeyNotFound's global, so errors.Is evaluates); laws:
// errIs_agree.
func ReqApplyPutIgnoreValue(lg *zap.Logger, le lease.Lessor, kv mvcc.KV, k []byte) {
	before, _, err := txn.Range(context.TODO(), lg, kv, &pb.RangeRequest{Key: k}, true)
	if err != nil {
		panic("apply-put-ignore-value: a current range failed")
	}
	presp, _, err := txn.Put(context.TODO(), lg, le, kv, &pb.PutRequest{Key: k, IgnoreValue: true})
	if len(before.Kvs) == 0 {
		if !errors.Is(err, srverrors.ErrKeyNotFound) || presp != nil {
			panic("apply-put-ignore-value: a missing key not refused")
		}
		return
	}
	if err != nil {
		panic("apply-put-ignore-value: a present key refused")
	}
	after, _, err := txn.Range(context.TODO(), lg, kv, &pb.RangeRequest{Key: k}, true)
	if err != nil || len(after.Kvs) != 1 || !bytes.Equal(after.Kvs[0].Value, before.Kvs[0].Value) {
		panic("apply-put-ignore-value: value changed")
	}
}

// REQ txn/apply-put-lease-check: a put on a lease the lessor does not hold fails with
// ErrLeaseNotFound, before any write.
// Users: apply/backend.go:51 (a put WithLease of a revoked or expired lease).
// Assumes: the sole writer; id is not a live lease of le (its Lease.lessorState), id != 0.
// Specs: Put.spec (putAns: W0's PutReq.check, the lease first; errIs: ErrLeaseNotFound's global);
// 3c's lessor.Lookup.spec, 3e's KV.Rev.contract.
func ReqApplyPutLeaseCheck(lg *zap.Logger, le lease.Lessor, kv mvcc.KV, k, v []byte, id int64) {
	if le.Lookup(lease.LeaseID(id)) != nil {
		return
	}
	rev := kv.Rev()
	_, _, err := txn.Put(context.TODO(), lg, le, kv, &pb.PutRequest{Key: k, Value: v, Lease: id})
	if !errors.Is(err, lease.ErrLeaseNotFound) {
		panic("apply-put-lease-check: a dead lease accepted")
	}
	if kv.Rev() != rev {
		panic("apply-put-lease-check: written anyway")
	}
}

// REQ txn/apply-delete-range: a range delete removes every present key of the range at one
// revision, the reply counting them.
// Users: apply/backend.go:55.
// Assumes: the sole writer.
// Specs: Range.spec, DeleteRange.spec.
func ReqApplyDeleteRange(lg *zap.Logger, kv mvcc.KV, k, end []byte) {
	before, _, err := txn.Range(context.TODO(), lg, kv, &pb.RangeRequest{Key: k, RangeEnd: end, CountOnly: true}, true)
	if err != nil {
		panic("apply-delete-range: a current range failed")
	}
	dresp, _, err := txn.DeleteRange(context.TODO(), lg, kv, &pb.DeleteRangeRequest{Key: k, RangeEnd: end})
	if err != nil {
		panic("apply-delete-range: a delete without PrevKv failed")
	}
	if dresp.Deleted != before.Count {
		panic("apply-delete-range: wrong count")
	}
	want := before.Header.Revision
	if dresp.Deleted > 0 {
		want++
	}
	if dresp.Header.Revision != want {
		panic("apply-delete-range: wrong revision")
	}
	after, _, err := txn.Range(context.TODO(), lg, kv, &pb.RangeRequest{Key: k, RangeEnd: end, CountOnly: true}, true)
	if err != nil || after.Count != 0 {
		panic("apply-delete-range: a key left")
	}
}

// REQ txn/apply-txn-cas: a compare-and-swap transaction takes the Then branch exactly when the
// comparison holds at the transaction's start, and its put is at the header's revision.
// Users: apply/backend.go:63 (a client's STM or lock: concurrency/stm.go, mutex.go), skip false.
// Assumes: the sole writer; the transaction passed checkTxnRequest/checkIntervals (txnSafe).
// Specs: Range.spec, Txn.spec (run, runRev); laws: run_txnRun; 3e's Mvcc.mvccState_reachable (a
// present key's mod revision is not 0).
func ReqApplyTxnCAS(lg *zap.Logger, le lease.Lessor, kv mvcc.KV, k, v []byte) {
	before, _, err := txn.Range(context.TODO(), lg, kv, &pb.RangeRequest{Key: k}, true)
	if err != nil {
		panic("apply-txn-cas: a current range failed")
	}
	rt := &pb.TxnRequest{
		Compare: []*pb.Compare{{Key: k, Target: pb.Compare_MOD, Result: pb.Compare_EQUAL,
			TargetUnion: &pb.Compare_ModRevision{ModRevision: 0}}},
		Success: []*pb.RequestOp{{Request: &pb.RequestOp_RequestPut{RequestPut: &pb.PutRequest{Key: k, Value: v}}}},
		Failure: []*pb.RequestOp{{Request: &pb.RequestOp_RequestRange{RequestRange: &pb.RangeRequest{Key: k}}}},
	}
	resp, _, err := txn.Txn(context.TODO(), lg, rt, false, kv, le, false)
	if err != nil {
		panic("apply-txn-cas: a checked transaction failed")
	}
	if resp.Succeeded != (len(before.Kvs) == 0) {
		panic("apply-txn-cas: wrong branch")
	}
	if len(resp.Responses) != 1 {
		panic("apply-txn-cas: wrong shape")
	}
	if resp.Succeeded {
		if resp.Responses[0].GetResponsePut() == nil || resp.Header.Revision != before.Header.Revision+1 {
			panic("apply-txn-cas: put not at the next revision")
		}
	} else if resp.Header.Revision != before.Header.Revision {
		panic("apply-txn-cas: a read moved the revision")
	}
}

// REQ txn/apply-txn-skip: with skipRangeExecution (no one waits for the result), the ranges are
// not run, their responses carry the transaction's revision only; the writes still happen.
// Users: apply/backend.go:63, apply/apply.go:43 (SkipRangeExecution when the proposer is not here).
// Assumes: the sole writer.
// Specs: Txn.spec (run at skip; run_txnRun: the events do not depend on skip); 3e's
// KV.Rev.contract.
func ReqApplyTxnSkip(lg *zap.Logger, le lease.Lessor, kv mvcc.KV, k, v []byte) {
	rev := kv.Rev()
	rt := &pb.TxnRequest{Success: []*pb.RequestOp{
		{Request: &pb.RequestOp_RequestPut{RequestPut: &pb.PutRequest{Key: k, Value: v}}},
		{Request: &pb.RequestOp_RequestRange{RequestRange: &pb.RangeRequest{Key: k}}},
	}}
	resp, _, err := txn.Txn(context.TODO(), lg, rt, false, kv, le, true)
	if err != nil {
		panic("apply-txn-skip: failed")
	}
	rr := resp.Responses[1].GetResponseRange()
	if rr == nil || len(rr.Kvs) != 0 || rr.Header.Revision != rev+1 || resp.Header.Revision != rev+1 {
		panic("apply-txn-skip: a skipped range executed, or a wrong revision")
	}
	if kv.Rev() != rev+1 {
		panic("apply-txn-skip: the put was not written")
	}
}

// REQ txn/apply-delete-prevkv: a delete with PrevKv returns the deleted key-values, in key order,
// as they were.
// Users: apply/backend.go:55 (a client's Delete WithPrevKV: client/v3/op.go; the leasing cache's
// and the STM's deletes).
// Assumes: the sole writer; context.TODO() (never done, so no context error).
// Specs: Range.spec, DeleteRange.spec.
func ReqApplyDeletePrevKv(lg *zap.Logger, kv mvcc.KV, k, end []byte) {
	before, _, err := txn.Range(context.TODO(), lg, kv, &pb.RangeRequest{Key: k, RangeEnd: end}, true)
	if err != nil {
		panic("apply-delete-prevkv: a current range failed")
	}
	dresp, _, err := txn.DeleteRange(context.TODO(), lg, kv, &pb.DeleteRangeRequest{Key: k, RangeEnd: end, PrevKv: true})
	if err != nil {
		panic("apply-delete-prevkv: the context is never done")
	}
	if len(dresp.PrevKvs) != len(before.Kvs) || dresp.Deleted != int64(len(before.Kvs)) {
		panic("apply-delete-prevkv: wrong count")
	}
	for i := range before.Kvs {
		if !bytes.Equal(dresp.PrevKvs[i].Key, before.Kvs[i].Key) ||
			!bytes.Equal(dresp.PrevKvs[i].Value, before.Kvs[i].Value) ||
			dresp.PrevKvs[i].ModRevision != before.Kvs[i].ModRevision {
			panic("apply-delete-prevkv: a previous key-value differs")
		}
	}
}

// REQ txn/apply-txn-check-fails: a transaction whose check fails (a put on a lease not live, or a
// range below the compaction) returns the sentinel, no response, and writes nothing, not even its
// other operations.
// Users: apply/backend.go:63 (3a's error results: ErrLeaseNotFound, ErrCompacted, ErrFutureRev
// mapped by togRPCError).
// Assumes: the sole writer; id != 0 is not a live lease of le.
// Specs: Txn.spec (run: opsCheck; errIs), 3c's lessor.Lookup.spec, 3e's KV.Rev.contract.
func ReqApplyTxnCheckFails(lg *zap.Logger, le lease.Lessor, kv mvcc.KV, k, v []byte, id int64) {
	if le.Lookup(lease.LeaseID(id)) != nil {
		return
	}
	rev := kv.Rev()
	rt := &pb.TxnRequest{Success: []*pb.RequestOp{
		{Request: &pb.RequestOp_RequestPut{RequestPut: &pb.PutRequest{Key: k, Value: v}}},
		{Request: &pb.RequestOp_RequestPut{RequestPut: &pb.PutRequest{Key: append(append([]byte{}, k...), 'x'), Value: v, Lease: id}}},
	}}
	resp, _, err := txn.Txn(context.TODO(), lg, rt, false, kv, le, false)
	if !errors.Is(err, lease.ErrLeaseNotFound) || resp != nil {
		panic("apply-txn-check-fails: a dead lease accepted")
	}
	if kv.Rev() != rev {
		panic("apply-txn-check-fails: written anyway")
	}
}
