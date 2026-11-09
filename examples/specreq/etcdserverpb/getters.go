// Package etcdserverpb holds the requirement snippets of etcd's v3 API messages (batch 3h):
// Spec/go_etcd_io/etcd/api/v3/etcdserverpb/.
package etcdserverpb

import (
	"bytes"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"google.golang.org/protobuf/proto"
)

// REQ etcdserverpb/txn-response-getters: a transaction's reply read through the oneof getters: the
// branch's range reply when the operation was a get, nil for another case (the client's Mutex,
// STM, recipes and Kubernetes read `Responses[0].GetResponseRange()`).
// Users: client/v3/concurrency/mutex.go (tryAcquire), stm.go (readSet.add),
// client/v3/kubernetes/client.go (kvFromTxnResponse), the recipes.
// Assumes: resp is a TxnResponse a Txn returned (txnRespOwn); its first operation was a get.
// Specs: ResponseOp.GetResponseRange.spec, ResponseOp.GetResponsePut.spec, RangeResponse.GetKvs.spec,
// ResponseHeader.GetRevision.spec; laws: txnRespOwn_unfold (W0).
func ReqTxnResponseGetters(resp *pb.TxnResponse) {
	if len(resp.Responses) == 0 {
		return
	}
	op := resp.Responses[0]
	if rr := op.GetResponseRange(); rr != nil {
		if op.GetResponsePut() != nil {
			panic("two cases of one oneof")
		}
		_ = len(rr.GetKvs())
		_ = rr.GetHeader().GetRevision()
	}
}

// REQ etcdserverpb/nil-header: a header read through nil (a streamed range's chunks but the last
// carry none; a watch response with no header) reads zero.
// Users: client/v3/watch.go (WatchResponse.IsProgressNotify), the cache's progress handling.
// Specs: ResponseHeader.GetRevision.spec (nil conjunct).
func ReqNilHeader(r *pb.RangeResponse) int64 {
	if r.GetHeader() == nil && r.GetHeader().GetRevision() != 0 {
		panic("nil header revision")
	}
	return r.GetHeader().GetRevision()
}

// REQ etcdserverpb/compare-key: a comparison's key read through its getter is the key it was built
// with, and a clone of the comparison has the same key (the client's cloneCompare).
// Users: client/v3/compare.go (Cmp.KeyBytes, cloneCompare), client/v3/leasing (evalCmp).
// Specs: Compare.GetKey.spec, proto's Clone.spec, compareOwn_msgAt.spec, holds_depth.spec.
func ReqCompareKey(key []byte) {
	c := &pb.Compare{Key: key, Target: pb.Compare_VERSION, Result: pb.Compare_EQUAL}
	if !bytes.Equal(c.GetKey(), key) {
		panic("compare key")
	}
	cl := proto.Clone(c).(*pb.Compare)
	if !bytes.Equal(cl.GetKey(), key) || cl.GetTarget() != pb.Compare_VERSION {
		panic("clone changed the comparison")
	}
}

// REQ etcdserverpb/request-range: a transaction's operation that is a range is read back as the
// range request it holds (the server's IsTxnReadonly; the trace attributes).
// Users: server/etcdserver/txn (IsTxnReadonly), server/etcdserver/tracing.go.
// Specs: RequestOp.GetRequestRange.spec, RangeRequest.GetKey.spec, RangeRequest.GetLimit.spec.
func ReqRequestRange(key []byte, limit int64) {
	op := &pb.RequestOp{Request: &pb.RequestOp_RequestRange{RequestRange: &pb.RangeRequest{Key: key, Limit: limit}}}
	r := op.GetRequestRange()
	if r == nil || !bytes.Equal(r.GetKey(), key) || r.GetLimit() != limit {
		panic("request range")
	}
}

// REQ etcdserverpb/sort-names: every sort order 0..2 and target 0..4 has a name; nothing else does
// (the client's Op.IsSortOptionValid).
// Users: client/v3/op.go (IsSortOptionValid).
// Specs: sortNames_init.spec.
func ReqSortNames() {
	for o := int32(0); o <= 2; o++ {
		if _, ok := pb.RangeRequest_SortOrder_name[o]; !ok {
			panic("sort order name")
		}
	}
	if _, ok := pb.RangeRequest_SortTarget_name[5]; ok {
		panic("sort target beyond VALUE")
	}
}
