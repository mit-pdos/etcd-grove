// Package etcdserverreq holds the requirement snippets of etcd's server request path (batch 2c,
// SpecPlan/Spec/go_etcd_io/etcd/server/v3/etcdserver/ApiReq.lean and the EtcdServer__*.lean specs of
// v3_server.go, and SpecPlan/Spec/.../etcdserver/read/): minimal uses of the patterns its users rely on (the
// gRPC handlers of api/v3rpc, the server's internal requesters: the lessor's expiry, the
// compactors, the alarms), each reliance an explicit panic.
//
// Common assumptions (the proofs' setting): s is a started member of a cluster (isServer), the
// caller owns the cluster's state etcdState in an invariant of its own, the keys a snippet names as
// "owned" are written by no other principal and attached to no lease, and ctx is a request context
// whose principal is the snippet's (reqPrin: no token, auth off; or a token of a user permitted
// what the snippet does). Requests are what the gRPC layer passes on (checkPutRequest,
// checkRangeRequest, checkTxnRequest at the configured --max-txn-ops).
package etcdserverreq

import (
	"bytes"
	"context"
	"errors"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/server/v3/auth"
	"go.etcd.io/etcd/server/v3/etcdserver"
	srverrors "go.etcd.io/etcd/server/v3/etcdserver/errors"
)

// REQ etcdserverreq/put-then-range: a linearizable range after an acknowledged put sees it, at a
// revision at least the put's; the key's mod revision is the put's revision.
// Users: api/v3rpc/key.go:53,95 (the handlers through RaftKV, as the client's put-then-get
// reaches them); examples/etcd/putget.
// Assumes: k is owned and non-empty.
// Specs: EtcdServer.Put.spec, EtcdServer.Range.spec (SrvCallTriple); laws: etcdState_lb,
// etcdLb_reach, putRespOwn_unfold, rangeRespOwn_unfold.
func ReqPutThenRange(ctx context.Context, s *etcdserver.EtcdServer, k, v []byte) {
	presp, err := s.Put(ctx, &pb.PutRequest{Key: k, Value: v})
	if err != nil {
		return
	}
	rresp, err := s.Range(ctx, &pb.RangeRequest{Key: k})
	if err != nil {
		return
	}
	if len(rresp.Kvs) != 1 || !bytes.Equal(rresp.Kvs[0].Value, v) {
		panic("put-then-range: lost write")
	}
	if rresp.Kvs[0].ModRevision != presp.Header.Revision {
		panic("put-then-range: wrong mod revision")
	}
	if rresp.Header.Revision < presp.Header.Revision {
		panic("put-then-range: revision went back")
	}
}

// REQ etcdserverreq/serializable-range: a serializable range answers from the member's view: never
// above a revision the cluster reached, its key-values those of that revision.
// Users: api/v3rpc/key.go:53 (a client's WithSerializable get), the corruption checker's reads.
// Assumes: k is owned and non-empty.
// Specs: EtcdServer.Range.spec; laws: etcdLb_ord, etcdLb_reach.
func ReqSerializableRange(ctx context.Context, s *etcdserver.EtcdServer, k []byte) {
	resp, err := s.Range(ctx, &pb.RangeRequest{Key: k, Serializable: true})
	if err != nil {
		return
	}
	if resp == nil || resp.Header == nil {
		panic("serializable-range: no reply")
	}
	if len(resp.Kvs) > 1 {
		panic("serializable-range: two values of one key")
	}
}

// REQ etcdserverreq/delete-then-range: a delete's reply counts the key it removed, and a later
// range does not see it.
// Users: api/v3rpc/key.go:104,53.
// Assumes: k is owned, non-empty and present (an earlier acknowledged put of this caller).
// Specs: EtcdServer.DeleteRange.spec, EtcdServer.Range.spec.
func ReqDeleteThenRange(ctx context.Context, s *etcdserver.EtcdServer, k []byte) {
	dresp, err := s.DeleteRange(ctx, &pb.DeleteRangeRequest{Key: k})
	if err != nil {
		return
	}
	if dresp.Deleted != 1 {
		panic("delete-then-range: wrong count")
	}
	rresp, err := s.Range(ctx, &pb.RangeRequest{Key: k})
	if err != nil {
		return
	}
	if len(rresp.Kvs) != 0 {
		panic("delete-then-range: deleted key seen")
	}
}

// REQ etcdserverreq/txn-cas: a write transaction comparing a key's mod revision commits its
// success branch exactly when the key was last written at that revision.
// Users: api/v3rpc/key.go:130 (Kubernetes' OptimisticPut through the client's Txn,
// concurrency's Mutex and STM).
// Assumes: k is owned and non-empty; rev is the mod revision of k at the caller's last
// acknowledged write of it.
// Specs: EtcdServer.Txn.spec (a write: one-shot update); laws: txnChecked_small (one compare, one
// put), txnRespOwn_unfold.
func ReqTxnCAS(ctx context.Context, s *etcdserver.EtcdServer, k, v []byte, rev int64) {
	resp, err := s.Txn(ctx, &pb.TxnRequest{
		Compare: []*pb.Compare{{Key: k, Target: pb.Compare_MOD, Result: pb.Compare_EQUAL,
			TargetUnion: &pb.Compare_ModRevision{ModRevision: rev}}},
		Success: []*pb.RequestOp{{Request: &pb.RequestOp_RequestPut{RequestPut: &pb.PutRequest{Key: k, Value: v}}}},
	})
	if err != nil {
		return
	}
	if !resp.Succeeded {
		panic("txn-cas: owned key changed")
	}
	if len(resp.Responses) != 1 || resp.Responses[0].GetResponsePut() == nil {
		panic("txn-cas: wrong responses")
	}
}

// REQ etcdserverreq/txn-readonly: a read-only transaction is a read: its answers are a range's.
// Users: api/v3rpc/key.go:130 (a client's If(...).Then(OpGet...) with no write).
// Assumes: k is owned, non-empty and present.
// Specs: EtcdServer.Txn.spec (a read: persistent update, Range's path); laws: txnChecked_small.
func ReqTxnReadOnly(ctx context.Context, s *etcdserver.EtcdServer, k []byte) {
	resp, err := s.Txn(ctx, &pb.TxnRequest{
		Success: []*pb.RequestOp{{Request: &pb.RequestOp_RequestRange{RequestRange: &pb.RangeRequest{Key: k}}}},
	})
	if err != nil {
		return
	}
	if !resp.Succeeded || len(resp.Responses) != 1 {
		panic("txn-readonly: wrong branch")
	}
	r := resp.Responses[0].GetResponseRange()
	if r == nil || len(r.Kvs) != 1 {
		panic("txn-readonly: owned key not seen")
	}
}

// REQ etcdserverreq/compactor-compact: a client's compaction at a revision the cluster reached
// never panics and, on success, has a reply with a header.
// Users: api/v3rpc/key.go:144.
// Assumes: rev ≥ 1 (the compactors never compact at 0, issues/etcd-restore-scheduled-compact-zero.md);
// the caller holds a gate share when physical (the handler's).
// Specs: EtcdServer.Compact.spec.
func ReqCompactorCompact(ctx context.Context, s *etcdserver.EtcdServer, rev int64, physical bool) {
	resp, err := s.Compact(ctx, &pb.CompactionRequest{Revision: rev, Physical: physical})
	if err != nil {
		return
	}
	if resp == nil || resp.Header == nil {
		panic("compact: no header")
	}
}

// REQ etcdserverreq/compactor-internal: the auto-compactor's compaction, from its own goroutine,
// with the context it built (a child of Background), holding no gate share, keeps running through
// the member's stop until Cleanup stops the compactor, and never panics.
// Users: api/v3compactor/periodic.go:142, revision.go:92 (Compactable.Compact, errors logged).
// Assumes: s was started (the compactor runs only from start: Compact before start panics on the
// nil wait registry); rev ≥ 1; the caller holds a thread token.
// Specs: EtcdServer.Compact.spec at phys = false (no srvGate: verify round, A7-completeness F1/F2);
// laws: ctxNoIncoming_background, ctxNoIncoming_child, reqPrin_noIncoming, reqCtxOk of a child of
// Background (4b's and otel's _background and _child laws).
func ReqCompactorInternal(s *etcdserver.EtcdServer, rev int64) {
	ctx, cancel := context.WithCancel(context.Background())
	defer cancel()
	_, _ = s.Compact(ctx, &pb.CompactionRequest{Revision: rev})
}

// REQ etcdserverreq/refusal-not-applied: a request the server refuses (too many requests, too large,
// an invalid token, a stale auth revision) did not take effect: the key is still absent.
// Users: the client's retry interceptor (client/v3/retry_interceptor.go: it resends after
// ErrAuthOldRevision and ErrInvalidAuthToken), api/v3rpc/key.go:95.
// Assumes: k is owned and absent.
// Specs: EtcdServer.Put.spec (outcome 1 with a refusal, or outcome 2: the update given back; every
// error with srvErrShape), EtcdServer.Range.spec; laws: srvErr_inj, srvErr_leaf
// (errors.Is against a sentinel is equality: Perennial's errors.wp_Is_leaf), srvErr_notCtx, the
// packages' initialization laws (sentinelAt: each global holds the sentinel of its e; errors_init).
func ReqRefusalNotApplied(ctx context.Context, s *etcdserver.EtcdServer, k, v []byte) {
	_, err := s.Put(ctx, &pb.PutRequest{Key: k, Value: v})
	if !errors.Is(err, srverrors.ErrTooManyRequests) && !errors.Is(err, srverrors.ErrRequestTooLarge) &&
		!errors.Is(err, auth.ErrAuthOldRevision) && !errors.Is(err, auth.ErrInvalidAuthToken) {
		return
	}
	rresp, err := s.Range(ctx, &pb.RangeRequest{Key: k})
	if err != nil {
		return
	}
	if len(rresp.Kvs) != 0 {
		panic("refusal: refused put applied")
	}
}

// REQ etcdserverreq/health-range: the health checks' range of the empty key never panics and, on
// success, finds nothing (no key is empty).
// Users: api/etcdhttp/health.go:224,435 (checkAPI, readCheck: KeysOnly, Limit 1, a WithRoot
// context; only err is used).
// Assumes: the caller holds a read permission over the cluster's state (W0's etcdPeek-like
// persistent update; the server's, 2e's).
// Specs: EtcdServer.Range.spec (srvStep's emptyRangeStep); laws: etcdLb_keyNonEmpty.
func ReqHealthRange(ctx context.Context, s *etcdserver.EtcdServer) {
	resp, err := s.Range(ctx, &pb.RangeRequest{KeysOnly: true, Limit: 1})
	if err != nil {
		return
	}
	if len(resp.Kvs) != 0 {
		panic("health-range: an empty key exists")
	}
}
