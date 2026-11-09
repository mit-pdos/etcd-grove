package etcdserverreq

import (
	"context"
	"errors"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/server/v3/etcdserver"
	srverrors "go.etcd.io/etcd/server/v3/etcdserver/errors"
	"go.etcd.io/raft/v3"
)

// REQ etcdserverreq/read-after-write: once LinearizableReadNotify returns nil, the member has
// applied every write acknowledged before the call: its store's revision is at least the write's.
// Users: read/read.go:74 (Range, RangeStream, a read-only Txn, Authenticate: v3_server.go:139,175,
// 346,838), interface.go:46 (the corruption checker's hasher, corrupt.go:187), the lease HTTP
// handler (server.go:688).
// Assumes: the put's reply was received before the call.
// Specs: EtcdServer.Put.spec, EtcdServer.LinearizableReadNotify.spec (verify round: a nil return
// gives a committed log extending the put's, with srvApplied of its length), EtcdServer.KV.spec; 2d's
// readReg_register/readReg_get (the put's answer fired before the read point), srvApplied_read,
// srvReadAt_mvcc, srvWatchable_mvcc (the Rev token), histAt; 3e's KV.Rev contract (the store's revision at a history
// point at or past the read point: assumed of 3e, not checked against its statement here).
func ReqReadAfterWrite(ctx context.Context, s *etcdserver.EtcdServer, k, v []byte) {
	presp, err := s.Put(ctx, &pb.PutRequest{Key: k, Value: v})
	if err != nil {
		return
	}
	if err := s.LinearizableReadNotify(ctx); err != nil {
		return
	}
	if s.KV().Rev() < presp.Header.Revision {
		panic("read-after-write: member behind an acknowledged write")
	}
}

// REQ etcdserverreq/read-error-indef: a linearizable read's wait fails only with an error after
// which the client learns nothing (the server stopping, a leader change, a timeout, the context's
// end): no definite answer is invented.
// Users: v3_server.go:141 (Range returns it as is; the handler maps it: ErrStopped, ErrLeaderChanged,
// ErrTimeout to their rpctypes errors, the context's errors to grpc's codes).
// Specs: EtcdServer.LinearizableReadNotify.spec (readErr, transparent: the server's sentinels srvErr
// .stopped, .leaderChanged, .timeout, raft's errIs ErrStopped, or a context's error),
// EtcdServer.readErr_indef; laws: srvErr_leaf (errors.Is is equality on the sentinels), srvErr_inj,
// errors_init (srverrors' globals hold those sentinels), raft's errs_init and errIs_agree.
func ReqReadErrIndef(ctx context.Context, s *etcdserver.EtcdServer) {
	err := s.LinearizableReadNotify(ctx)
	if err == nil {
		return
	}
	if !errors.Is(err, srverrors.ErrStopped) && !errors.Is(err, srverrors.ErrLeaderChanged) &&
		!errors.Is(err, srverrors.ErrTimeout) && !errors.Is(err, raft.ErrStopped) &&
		!errors.Is(err, context.Canceled) && !errors.Is(err, context.DeadlineExceeded) {
		panic("read-error: unexpected error")
	}
}
