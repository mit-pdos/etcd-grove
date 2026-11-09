package txn

import (
	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/server/v3/etcdserver/txn"
)

// REQ txn/readonly-kinds: a transaction of ranges only is read-only (and serializable if every
// range is); the empty transaction is both (issues/etcd-txn-empty-serializable.md); one with a put,
// a delete or a nested transaction is not read-only.
// Users: v3_server.go:326,345 (EtcdServer.Txn's dispatch: local read or raft proposal).
// Assumes: none.
// Specs: IsTxnReadonly.spec, IsTxnSerializable.spec (W0's TxnReq.readonly, TxnReq.serializable).
func ReqReadonlyKinds(k []byte) {
	empty := &pb.TxnRequest{}
	if !txn.IsTxnReadonly(empty) || !txn.IsTxnSerializable(empty) {
		panic("readonly-kinds: the empty transaction")
	}
	ser := &pb.TxnRequest{Failure: []*pb.RequestOp{
		{Request: &pb.RequestOp_RequestRange{RequestRange: &pb.RangeRequest{Key: k, Serializable: true}}}}}
	if !txn.IsTxnReadonly(ser) || !txn.IsTxnSerializable(ser) {
		panic("readonly-kinds: a serializable read")
	}
	nested := &pb.TxnRequest{Success: []*pb.RequestOp{
		{Request: &pb.RequestOp_RequestTxn{RequestTxn: &pb.TxnRequest{}}}}}
	if txn.IsTxnReadonly(nested) {
		panic("readonly-kinds: a nested transaction counted as a read")
	}
	put := &pb.TxnRequest{Success: []*pb.RequestOp{
		{Request: &pb.RequestOp_RequestPut{RequestPut: &pb.PutRequest{Key: k}}}}}
	if txn.IsTxnReadonly(put) || txn.IsTxnSerializable(put) {
		panic("readonly-kinds: a put counted as a read")
	}
}

// REQ txn/sort-helpers: the gRPC layer's range check: the default ordering is no order or
// ascending by key; a revision filter is any of the four set.
// Users: api/v3rpc/key.go:173,176 (checkRangeRequest: a limit with a sort or a filter).
// Assumes: none.
// Specs: IsDefaultOrdering.spec, HasRevisionFilters.spec.
func ReqSortHelpers(r *pb.RangeRequest) {
	if !txn.IsDefaultOrdering(pb.RangeRequest_KEY, pb.RangeRequest_ASCEND) ||
		!txn.IsDefaultOrdering(pb.RangeRequest_VALUE, pb.RangeRequest_NONE) ||
		txn.IsDefaultOrdering(pb.RangeRequest_KEY, pb.RangeRequest_DESCEND) {
		panic("sort-helpers: the default ordering")
	}
	if txn.HasRevisionFilters(r) != (r.MinModRevision != 0 || r.MaxModRevision != 0 ||
		r.MinCreateRevision != 0 || r.MaxCreateRevision != 0) {
		panic("sort-helpers: revision filters")
	}
}
