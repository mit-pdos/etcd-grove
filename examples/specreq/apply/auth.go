package apply

import (
	"errors"

	"go.uber.org/zap"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/pkg/v3/wait"
	"go.etcd.io/etcd/server/v3/auth"
	"go.etcd.io/etcd/server/v3/etcdserver/apply"
	"go.etcd.io/etcd/server/v3/etcdserver/txn"
	"go.etcd.io/etcd/server/v3/lease"
	"go.etcd.io/raft/v3/raftpb"
)

// REQ apply/stale-revision: a write whose header carries an auth revision older than the store's
// is refused with ErrAuthOldRevision and changes nothing (the client's interceptor resends it with
// a fresh token; 2c keeps its update unfired).
// Users: server/etcdserver/v3_server.go (raftRequest: the header's AuthRevision), 2c's
// processInternalRaftRequestOnce (outcome 2 for ErrAuthOldRevision).
// Assumes: auth is enabled; no NOSPACE or CORRUPT alarm is raised (they refuse first); e is a
// committed put by a user with a nonzero auth revision below the store's (an auth change committed
// after its token); this goroutine is the apply thread.
// Specs: Apply.spec, isUber_apply; laws: irrStep_oldRev (nothing changed), irrStep_step.
func ReqStaleRevision(lg *zap.Logger, e *raftpb.Entry, ua apply.UberApplier, w wait.Wait) {
	ar, _ := apply.Apply(lg, e, ua, w, true)
	if ar != nil && !errors.Is(ar.Err, auth.ErrAuthOldRevision) {
		panic("stale-revision: a stale write applied")
	}
}

// REQ apply/check-txn-auth: the request path's check of a serializable read-only transaction passes
// with auth disabled, and its error is a permission error otherwise.
// Users: server/etcdserver/v3_server.go:355 (Txn's doSerialize check).
// Assumes: as is the member's auth store, read concurrently with the apply thread.
// Specs: CheckTxnAuth.spec (its premise: a read-only transaction, as 2c's only call), txn's
// IsTxnReadonly.spec.
func ReqCheckTxnAuth(as auth.AuthStore, le lease.Lessor, ai *auth.AuthInfo, rt *pb.TxnRequest) {
	if !txn.IsTxnReadonly(rt) {
		return
	}
	err := apply.CheckTxnAuth(as, ai, le, rt)
	if err != nil && !errors.Is(err, auth.ErrUserEmpty) && !errors.Is(err, auth.ErrAuthOldRevision) &&
		!errors.Is(err, auth.ErrPermissionDenied) {
		panic("check-txn-auth: an error that is not a permission error")
	}
}
