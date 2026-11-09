// Package apply holds the requirement snippets of etcd's apply layer (batch 3a): what the apply
// thread (2d) and the request path (2c) rely on of apply.Apply, the uber-applier and CheckTxnAuth.
package apply

import (
	"errors"

	"go.uber.org/zap"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/pkg/v3/wait"
	"go.etcd.io/etcd/server/v3/etcdserver/apply"
	errs "go.etcd.io/etcd/server/v3/etcdserver/errors"
	"go.etcd.io/raft/v3/raftpb"
)

// REQ apply/new-uber: an uber-applier is built over the member's stores at any state (after a
// restart, after a snapshot install), whatever alarms are raised.
// Users: server/etcdserver/server.go:357 (NewServer), server/etcdserver/server.go:1181
// (applySnapshot).
// Assumes: opts holds the member's stores (mvcc, lessor, auth store, alarm store, membership,
// backend), its raft status, snapshot server and consistent indexer, and a logger.
// Specs: NewUberApplier.spec; laws: isUber_apply.
func ReqNewUber(opts apply.ApplierOptions) apply.UberApplier {
	ua := apply.NewUberApplier(opts)
	if ua == nil {
		panic("new-uber: nil applier")
	}
	return ua
}

// REQ apply/write: a committed write whose waiter is registered is applied, its result is the
// answer the model's step gives (a put's reply), or the quota's ErrNoSpace, which settles nothing
// (the write may be applied: the caller treats it as unsettled), and its id is the entry's.
// Users: server/etcdserver/server.go:1994 (applyEntryNormal), its waiter v3_server.go:1019
// (`resp.(*pb.PutResponse)`).
// Assumes: e is a committed normal entry whose data is the marshalled InternalRaftRequest of a valid
// put with id `id` (the request path's), its lease (if any) live; auth is disabled; no alarm is raised;
// this goroutine is the apply thread.
// Specs: Apply.spec, isUber_apply (uberApplier.Apply.spec); laws: irrStep_step, applyStep_fun.
func ReqApplyWrite(lg *zap.Logger, e *raftpb.Entry, ua apply.UberApplier, w wait.Wait, id uint64) {
	ar, gotID := apply.Apply(lg, e, ua, w, true)
	if gotID != id {
		panic("write: wrong id")
	}
	if ar == nil {
		return // the requester gave up meanwhile (Trigger(id, nil)): nothing owed
	}
	if errors.Is(ar.Err, errs.ErrNoSpace) {
		return // over the quota: unsettled
	}
	if ar.Err != nil {
		panic("write: a valid put refused")
	}
	if _, ok := ar.Resp.(*pb.PutResponse); !ok {
		panic("write: not a put's reply")
	}
}

// REQ apply/replay: below the consistent index (shouldApplyV3 false) a KV entry changes nothing
// and answers nil.
// Users: server/etcdserver/server.go:1934-1945 (apply: the replay after a restart).
// Assumes: e is a committed normal entry of a put (as in ReqApplyWrite); this goroutine is the
// apply thread.
// Specs: Apply.spec, isUber_apply (its replay clause: `ar = null`); laws: irrStep_noV3.
func ReqApplyReplay(lg *zap.Logger, e *raftpb.Entry, ua apply.UberApplier, w wait.Wait) {
	ar, _ := apply.Apply(lg, e, ua, w, false)
	if ar != nil {
		panic("replay: the replay answered")
	}
}

// REQ apply/no-result: a read no one waits for may be skipped; either way it is safe, and nothing is
// owed to a waiter.
// Users: server/etcdserver/server.go:1994-2001 (applyEntryNormal's nil path).
// Assumes: e's request is a Range (or AuthStatus, UserGet, RoleGet) entry; this goroutine is the
// apply thread.
// Specs: Apply.spec (waitDone on the nil path); laws: irrStep_read.
func ReqApplyNoResult(lg *zap.Logger, e *raftpb.Entry, ua apply.UberApplier, w wait.Wait) {
	_, _ = apply.Apply(lg, e, ua, w, true)
}
