package txn

import (
	"errors"
	"time"

	"go.uber.org/zap"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/server/v3/etcdserver/txn"
)

// REQ txn/warn-read-only: the request path's deferred warnings take the request as its stringer and
// the reply, nil, or (a read-only transaction stopped by its context) a partly filled response, and
// return; the reply is still the caller's after.
// Users: v3_server.go:126 (EtcdServer.Range's defer), :359 (EtcdServer.Txn's read-only defer).
// Assumes: lg is the server's logger; resp is Range's or Txn's result for r.
// Specs: WarnOfExpensiveReadOnlyRangeRequest.spec, WarnOfExpensiveReadOnlyTxnRequest.spec (3h's
// stringerOk of a request), Range.spec, Txn.spec (roTxnResp after a context error).
func ReqWarnReadOnly(lg *zap.Logger, r *pb.RangeRequest, resp *pb.RangeResponse, rt *pb.TxnRequest,
	tresp *pb.TxnResponse, err error) {
	start := time.Now()
	txn.WarnOfExpensiveReadOnlyRangeRequest(lg, 0, start, r, resp, err)
	txn.WarnOfExpensiveReadOnlyTxnRequest(lg, 0, start, rt, tresp, err)
	if resp != nil && resp.Header == nil {
		panic("warn-read-only: the reply changed")
	}
}

// REQ txn/warn-apply: the uber applier's deferred warnings take an InternalRaftStringer of the
// entry's request and the apply's response (a reply it built, or nil) and return.
// Users: apply/uber_applier.go:98-101 (dispatch's defer: ApplySecObserve, WarnOfExpensiveRequest,
// WarnOfFailedRequest).
// Assumes: ir is the committed request; resp is the apply's reply message of it (owned: its content
// within protobuf's depth, msgOpt), or nil.
// Specs: ApplySecObserve.spec, WarnOfExpensiveRequest.spec, WarnOfFailedRequest.spec (3h's
// stringerOk of an InternalRaftStringer).
func ReqWarnApply(lg *zap.Logger, ir *pb.InternalRaftRequest, resp *pb.PutResponse) {
	start := time.Now()
	txn.ApplySecObserve("v3", "Put", resp != nil, time.Since(start))
	txn.WarnOfExpensiveRequest(lg, 0, start, &pb.InternalRaftStringer{Request: ir}, resp, nil)
	txn.WarnOfFailedRequest(lg, start, &pb.InternalRaftStringer{Request: ir}, resp, errors.New("x"))
}
