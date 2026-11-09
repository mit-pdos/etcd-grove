// Package apply holds the requirement snippets of etcd's apply layer (batch 3a): what the apply
// thread (2d) and the request path (2c) rely on of apply.Apply, the uber-applier and CheckTxnAuth.
package apply

import (
	"go.uber.org/zap"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/pkg/v3/wait"
	"go.etcd.io/etcd/server/v3/etcdserver/apply"
	"go.etcd.io/etcd/server/v3/storage/mvcc"
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

// REQ apply/write: a committed write is applied once, its result is the answer the model's step
// gives at the store's state (a put at the next revision), and its id is the entry's request id.
// Users: server/etcdserver/server.go:1994 (applyEntryNormal), its waiter v3_server.go:1019
// (`resp.(*pb.PutResponse)`).
// Assumes: e is a committed normal entry whose data is the marshalled InternalRaftRequest of a valid
// put with id `id` (the request path's); auth is disabled; no alarm is raised; the backend is under
// its quota; kv is the store of ua's options and this goroutine is the apply thread.
// Specs: Apply.spec, isUber_apply (uberApplier.Apply.spec); laws: irrStep_step, applyStep_fun.
func ReqApplyWrite(lg *zap.Logger, e *raftpb.Entry, ua apply.UberApplier, w wait.Wait, kv mvcc.KV, id uint64) {
	before := kv.Rev()
	ar, gotID := apply.Apply(lg, e, ua, w, true)
	if gotID != id {
		panic("write: wrong id")
	}
	if ar == nil || ar.Err != nil {
		panic("write: a valid put refused")
	}
	resp, ok := ar.Resp.(*pb.PutResponse)
	if !ok || resp.Header.Revision != before+1 || kv.Rev() != before+1 {
		panic("write: not the put's step")
	}
}

// REQ apply/replay: below the consistent index (shouldApplyV3 false) a KV entry changes nothing
// and answers nil.
// Users: server/etcdserver/server.go:1934-1945 (apply: the replay after a restart).
// Assumes: e is a committed normal entry of a put (as in ReqApplyWrite); this goroutine is the
// apply thread.
// Specs: Apply.spec, isUber_apply; laws: irrStep_noV3.
func ReqApplyReplay(lg *zap.Logger, e *raftpb.Entry, ua apply.UberApplier, w wait.Wait, kv mvcc.KV) {
	before := kv.Rev()
	ar, _ := apply.Apply(lg, e, ua, w, false)
	if ar != nil || kv.Rev() != before {
		panic("replay: the replay changed the store or answered")
	}
}

// REQ apply/no-result: a read no one waits for is not applied, and nothing changes.
// Users: server/etcdserver/server.go:1994 (another member's linearizable-path range entry, legacy).
// Assumes: e's request is a Range (or AuthStatus, UserGet, RoleGet) whose id is not registered in w;
// this goroutine is the apply thread.
// Specs: Apply.spec; laws: irrStep_step (a read's Step changes nothing).
func ReqApplyNoResult(lg *zap.Logger, e *raftpb.Entry, ua apply.UberApplier, w wait.Wait, kv mvcc.KV) {
	before := kv.Rev()
	_, _ = apply.Apply(lg, e, ua, w, true)
	if kv.Rev() != before {
		panic("no-result: a read changed the store")
	}
}
