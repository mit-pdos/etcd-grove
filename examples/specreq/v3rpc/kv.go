// Package v3rpc holds the requirement snippets of etcd's gRPC services (batch 2a,
// Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/Api.lean): what a client of a member's KV,
// Lease, Auth, Cluster and Maintenance services relies on, over the raw generated clients (as the
// Go client's retry wrappers call them), each reliance an explicit panic.
//
// Common assumptions: kc, lc, ac, mc are generated clients over a connection to members of one
// cluster (servesAt, Api.lean's servesAt_addr); the caller owns the cluster's state in an
// invariant of its own; a key a snippet calls "owned" is written by no other principal; auth is
// off unless the snippet says otherwise. Errors the callers handle as indefinite (a timeout, the
// leader lost, a transport error) are returned.
package v3rpc

import (
	"context"
	"errors"
	"io"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/api/v3/v3rpc/rpctypes"
)

// REQ v3rpc/validation-answer: the gRPC layer's validation errors are the cluster's answers (a
// definite error, the request linearized as a no-op), never an indefinite error: an empty key, a
// value with IgnoreValue, too many operations, a key put twice in a transaction.
// Users: the client's kv.Do (rpctypes.Error of the status: errVal e), txnlin's call (a definite
// error is "applied as a no-op"), Kubernetes' store (ErrDuplicateKey is a bug of its own).
// Assumes: the member's --max-txn-ops is 128 (the default; at most 4999, Api.lean's maxTxnOpsMax).
// Specs: kvServer.Put.spec, kvServer.Txn.spec, checkPutRequest.spec, checkTxnRequest.spec,
// checkIntervals.spec; the contract etcdUnary's first way; rpctypes' Error.spec, init.spec.
func ReqValidationAnswer(ctx context.Context, kc pb.KVClient) {
	_, err := kc.Put(ctx, &pb.PutRequest{Key: nil, Value: []byte("v")})
	if err != nil && rpctypes.Error(err) != rpctypes.ErrEmptyKey && !indefinite(err) {
		panic("validation: an empty key's put fails with another definite error")
	}
	if err == nil {
		panic("validation: an empty key's put succeeded")
	}
	_, err = kc.Put(ctx, &pb.PutRequest{Key: []byte("k"), Value: []byte("v"), IgnoreValue: true})
	if err == nil || (rpctypes.Error(err) != rpctypes.ErrValueProvided && !indefinite(err)) {
		panic("validation: a value with IgnoreValue")
	}
	put := &pb.RequestOp{Request: &pb.RequestOp_RequestPut{RequestPut: &pb.PutRequest{Key: []byte("k"), Value: []byte("v")}}}
	_, err = kc.Txn(ctx, &pb.TxnRequest{Success: []*pb.RequestOp{put, put}})
	if err == nil || (rpctypes.Error(err) != rpctypes.ErrDuplicateKey && !indefinite(err)) {
		panic("validation: a key put twice in one branch")
	}
}

// REQ v3rpc/put-then-range: a put's reply revision is the cluster's; a linearizable range after it
// sees the put (the read's update fired at a state after the put's).
// Users: txnlin, putget, Kubernetes' store (read-your-writes).
// Assumes: k owned.
// Specs: kvServer.Put.spec, kvServer.Range.spec (quotaKVServer's), the contract's first way; W0's
// Step, etcdLb_reach.
func ReqPutThenRange(ctx context.Context, kc pb.KVClient, k string) {
	pr, err := kc.Put(ctx, &pb.PutRequest{Key: []byte(k), Value: []byte("v1")})
	if err != nil {
		return
	}
	rr, err := kc.Range(ctx, &pb.RangeRequest{Key: []byte(k)})
	if err != nil {
		return
	}
	if rr.Header.Revision < pr.Header.Revision || len(rr.Kvs) != 1 || string(rr.Kvs[0].Value) != "v1" {
		panic("put-then-range: a linearizable read missed an acknowledged put")
	}
}

// REQ v3rpc/compact-admin: with auth on, a compaction by a principal that is not root is refused
// (ErrPermissionDenied, ErrUserEmpty, ErrUserNotFound: definite, nothing compacted), never
// applied.
// Users: Kubernetes' compactor (runs as root), etcdctl compaction, examples/etcd/compacted.
// Assumes: auth on; ctx's token names a user without the root role; no other compaction.
// Specs: kvServer.Compact.spec (AuthAdmin.isPermitted.spec); the model's compact step with its admin
// refusal (req/go_etcd_io_etcd_api_v3.md, from 2a).
func ReqCompactAdmin(ctx context.Context, kc pb.KVClient, rev int64) {
	_, err := kc.Compact(ctx, &pb.CompactionRequest{Revision: rev})
	if err == nil {
		panic("compact-admin: a non-root principal compacted")
	}
}

// REQ v3rpc/lease-ttl-unknown: TimeToLive of a lease the member does not know is a reply with TTL
// -1 and the request's ID, not an error.
// Users: the client's lessor.TimeToLive (1c's leaseTTLReply), concurrency's Session (a lost lease),
// Kubernetes' lease manager.
// Assumes: id was never granted.
// Specs: LeaseServer.LeaseTimeToLive.spec (ansOutcome's case).
func ReqLeaseTTLUnknown(ctx context.Context, lc pb.LeaseClient, id int64) {
	resp, err := lc.LeaseTimeToLive(ctx, &pb.LeaseTimeToLiveRequest{ID: id})
	if err != nil {
		if rpctypes.Error(err) == rpctypes.ErrLeaseNotFound {
			panic("lease-ttl-unknown: an error, not a reply")
		}
		return
	}
	if resp.TTL != -1 || resp.ID != id {
		panic("lease-ttl-unknown: a never-granted lease has a TTL")
	}
}

// REQ v3rpc/range-stream: a streamed range's chunks, read until io.EOF, are the range's answer at
// one revision; only the last carries a header.
// Users: the client's kv.GetStream (W0's wireStreamAt_recv), Kubernetes' streamed lists.
// Assumes: the range uses the default order and no revision filter; no compaction during it.
// Specs: kvServer.RangeStream.spec, headerFillingRangeStream.Send.spec, rangeStreamSpec (Api.lean),
// rsSink_intro, rsSink_out; Grpc's cliRecv_recv.
func ReqRangeStream(ctx context.Context, kc pb.KVClient, prefix string) {
	end := []byte(prefix)
	end[len(end)-1]++
	sc, err := kc.RangeStream(ctx, &pb.RangeRequest{Key: []byte(prefix), RangeEnd: end})
	if err != nil {
		return
	}
	var last *pb.RangeResponse
	for {
		m, err := sc.Recv()
		if err != nil {
			if last != nil && last.Header == nil && errors.Is(err, io.EOF) {
				panic("range-stream: the last chunk has no header")
			}
			return
		}
		if last != nil && last.Header != nil {
			panic("range-stream: a chunk after the one with the header")
		}
		last = m.RangeResponse
	}
}

// indefinite: an error the client treats as settling nothing (not one of etcd's definite errors).
func indefinite(err error) bool {
	e := rpctypes.Error(err)
	switch e {
	case rpctypes.ErrNoLeader, rpctypes.ErrTimeout, rpctypes.ErrStopped, rpctypes.ErrLeaderChanged,
		rpctypes.ErrTimeoutDueToLeaderFail, rpctypes.ErrTimeoutDueToConnectionLost, rpctypes.ErrNotCapable:
		return true
	}
	_, isEtcd := e.(rpctypes.EtcdError)
	return !isEtcd
}
