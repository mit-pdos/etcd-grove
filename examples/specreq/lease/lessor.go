// Requirement snippets for server/lease, the lessor (batch 3c): what the apply thread (3a's
// applier, 3b's txn, 3e's mvcc, 2d's applySnapshot), the request path (2c) and the server's
// lifecycle (2d, 2e) rely on.
package lease

import (
	"context"
	"errors"
	"net/http"
	"sync/atomic"

	"github.com/Masterminds/semver/v3"
	"go.uber.org/zap"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/pkg/v3/traceutil"
	"go.etcd.io/etcd/server/v3/lease"
	"go.etcd.io/etcd/server/v3/lease/leasehttp"
	"go.etcd.io/etcd/server/v3/storage/backend"
	"go.etcd.io/etcd/server/v3/storage/mvcc"
)

// REQ lease/grant-lookup: a grant of a non-zero id that is not live, with a TTL at most
// MaxLeaseTTL, succeeds; the lease is then live with its object's ID and a TTL raised to the
// minimum; a second grant of it is ErrLeaseExists, a grant of id 0 ErrLeaseNotFound, a TTL above
// MaxLeaseTTL ErrLeaseTTLTooLarge.
// Users: server/etcdserver/apply/backend.go:84 (LeaseGrant: l.ID, l.TTL()), txn/put.go:83 and
// apply/auth.go:199 (Lookup at the writer), v3_server.go:652 (TTL()).
// Assumes: the caller is the lessor's writer (lessorState) inside an apply (the backend's hook
// contract, beHook); id ≠ 0 is not live; ttl ≤ MaxLeaseTTL; the lessor was made with MinLeaseTTL minTTL.
// Specs: lessor.Grant.spec, lessor.Lookup.spec, Lease.TTL.spec; laws: lessorState_at,
// lessorState_le, lessorAt_agree, lessorAt_obj, leaseObj_id, init.
func ReqGrantLookup(le lease.Lessor, id lease.LeaseID, ttl, minTTL int64) {
	l, err := le.Grant(id, ttl)
	if err != nil {
		panic("grant-lookup: grant refused")
	}
	want := ttl
	if want < minTTL {
		want = minTTL
	}
	if l.ID != id || l.TTL() != want {
		panic("grant-lookup: wrong lease")
	}
	if le.Lookup(id) != l {
		panic("grant-lookup: lease not live")
	}
	if _, err := le.Grant(id, ttl); err != lease.ErrLeaseExists {
		panic("grant-lookup: granted twice")
	}
	if _, err := le.Grant(lease.NoLease, ttl); err != lease.ErrLeaseNotFound {
		panic("grant-lookup: granted lease 0")
	}
	if _, err := le.Grant(id, lease.MaxLeaseTTL+1); err != lease.ErrLeaseTTLTooLarge {
		panic("grant-lookup: TTL above the maximum")
	}
}

// REQ lease/attach-detach: mvcc's put and delete: a key attached to a live lease is reported by
// GetLease and Keys; Attach never fails on a live lease (mvcc panics if it does); detached, the key
// has no lease; Attach to a lease not live is ErrLeaseNotFound.
// Users: server/storage/mvcc/kvstore_txn.go:233-290 (put), 335-345 (delete), kvstore.go:398
// (restore).
// Assumes: the caller is the writer; id is live, id+1 is not; k is on no lease.
// Specs: lessor.GetLease.spec, lessor.Attach.spec, lessor.Detach.spec, lessor.Lookup.spec,
// Lease.Keys.spec.
func ReqAttachDetach(le lease.Lessor, id lease.LeaseID, k string) {
	items := []lease.LeaseItem{{Key: k}}
	if le.GetLease(items[0]) != lease.NoLease {
		panic("attach-detach: key already leased")
	}
	if err := le.Attach(id, items); err != nil {
		panic("unexpected error from lease Attach")
	}
	if le.GetLease(items[0]) != id {
		panic("attach-detach: GetLease lost the key")
	}
	found := false
	for _, x := range le.Lookup(id).Keys() {
		found = found || x == k
	}
	if !found {
		panic("attach-detach: Keys lost the key")
	}
	if err := le.Detach(id, items); err != nil {
		panic("attach-detach: detach refused")
	}
	if le.GetLease(items[0]) != lease.NoLease {
		panic("attach-detach: key still leased")
	}
	if err := le.Attach(id+1, items); err != lease.ErrLeaseNotFound {
		panic("attach-detach: attached to a lease not live")
	}
}

// recordDel is a range deleter in mvcc's shape: it holds the batch transaction's lock from rd()
// to End(), and its delete detaches the key from its lease (as mvcc's delete does).
type recordDel struct {
	le    lease.Lessor
	tx    backend.BatchTx
	keys  []string
	ended bool
}

func (d *recordDel) DeleteRange(key, end []byte) (int64, int64) {
	item := lease.LeaseItem{Key: string(key)}
	if id := d.le.GetLease(item); id != lease.NoLease {
		_ = d.le.Detach(id, []lease.LeaseItem{item})
	}
	d.keys = append(d.keys, string(key))
	return 1, 0
}

func (d *recordDel) End() {
	d.ended = true
	d.tx.Unlock()
}

// REQ lease/revoke-deletes: Revoke deletes exactly the lease's keys, in sorted order, through the
// range deleter, in one deletion transaction it ends; the lease is gone after it; a second Revoke
// is ErrLeaseNotFound.
// Users: server/etcdserver/apply/backend.go:95 (LeaseRevoke, from a client's revoke or the
// leader's expiry revocation, server.go:882); the deleter is mvcc's (kvstore.go:117,
// watchable_store.go:107).
// Assumes: the caller is the writer inside an apply; be is the lessor's backend; id is live with
// exactly the keys a < b attached (and no other lease names them).
// Specs: lessor.SetRangeDeleter.spec, lessor.Attach.spec, lessor.Revoke.spec (rdOk), Lookup,
// GetLease.
func ReqRevokeDeletes(le lease.Lessor, be backend.Backend, id lease.LeaseID, a, b string) {
	var d *recordDel
	le.SetRangeDeleter(func() lease.TxnDelete {
		tx := be.BatchTx()
		tx.LockInsideApply()
		d = &recordDel{le: le, tx: tx}
		return d
	})
	if err := le.Revoke(id); err != nil {
		panic("revoke-deletes: revoke refused")
	}
	if d == nil || !d.ended || len(d.keys) != 2 || d.keys[0] != a || d.keys[1] != b {
		panic("revoke-deletes: not the lease's keys, sorted, in one ended transaction")
	}
	if le.Lookup(id) != nil || le.GetLease(lease.LeaseItem{Key: a}) != lease.NoLease {
		panic("revoke-deletes: lease still live")
	}
	if err := le.Revoke(id); err != lease.ErrLeaseNotFound {
		panic("revoke-deletes: revoked twice")
	}
}

// REQ lease/leases-list: Leases lists every live lease once (LeaseLeases' ids).
// Users: server/etcdserver/v3_server.go:738 (LeaseLeases).
// Assumes: the leases live are exactly ids (distinct), and nothing grants, revokes or recovers
// meanwhile; the caller has a reader token.
// Specs: lessor.Leases.spec; laws: lessorAt_obj, leaseObj_id.
func ReqLeasesList(le lease.Lessor, ids []lease.LeaseID) {
	ls := le.Leases()
	if len(ls) != len(ids) {
		panic("leases-list: wrong count")
	}
	seen := map[lease.LeaseID]bool{}
	for _, l := range ls {
		if seen[l.ID] {
			panic("leases-list: a lease twice")
		}
		seen[l.ID] = true
	}
	for _, id := range ids {
		if !seen[id] {
			panic("leases-list: a live lease missing")
		}
	}
}

// REQ lease/reader-lower-bound: a reader on another goroutine, told of a grant (through a channel:
// the writer's history index as a lower bound), finds the lease (and its keys among those attached
// meanwhile), never an older state.
// Users: server/etcdserver/v3_server.go:512, 592, 624, 645 (the request path's Lookup after
// waitAppliedIndex), 738 (Leases).
// Assumes: the lease is never revoked nor recovered over (every later state has it live); done
// carries the grant's happening (lessorLb); the caller has a reader token (lessorReaders).
// Specs: lessor.Lookup.spec, Lease.Keys.spec (any goroutine, lessorLb).
func ReqReaderLowerBound(le lease.Lessor, id lease.LeaseID, done <-chan struct{}) {
	<-done
	l := le.Lookup(id)
	if l == nil || l.ID != id {
		panic("reader-lower-bound: an older state")
	}
	_ = l.Keys()
}

// REQ lease/renew: a renewal answers the lease's TTL, ErrLeaseNotFound (not live), or
// ErrNotPrimary (forwarded to the leader by the caller); never another error.
// Users: server/etcdserver/v3_server.go:528 (LeaseRenew on the leader).
// Assumes: id was granted (before the caller's lower bound) and is never revoked nor recovered
// over (the caller's invariant: every later state has id live at the same object); the lessor's
// checkpointer is nil or the server's (ckptOk).
// Specs: lessor.Renew.spec, lessor.Lookup.spec, Lease.TTL.spec, SetCheckpointer.spec.
func ReqRenew(le lease.Lessor, id lease.LeaseID) {
	ttl, err := le.Renew(id)
	switch err {
	case nil:
		if ttl != le.Lookup(id).TTL() {
			panic("renew: not the granted TTL")
		}
	case lease.ErrNotPrimary:
	case lease.ErrLeaseNotFound:
		panic("renew: a live lease not found")
	default:
		panic("renew: an unexpected error")
	}
}

// REQ lease/checkpoint-noop: a checkpoint changes nothing a reader sees and never fails.
// Users: server/etcdserver/apply/backend.go:101 (LeaseCheckpoint).
// Assumes: the caller is the writer inside an apply; id is live.
// Specs: lessor.Checkpoint.spec, lessor.Lookup.spec.
func ReqCheckpointNoop(le lease.Lessor, id lease.LeaseID, rem int64) {
	l := le.Lookup(id)
	if err := le.Checkpoint(id, rem); err != nil {
		panic("checkpoint-noop: checkpoint failed")
	}
	if le.Lookup(id) != l {
		panic("checkpoint-noop: lease changed")
	}
}

// REQ lease/recover: after Recover over a backend whose lease bucket holds ids, exactly those
// leases are live, with no key attached (mvcc's Restore re-attaches them next).
// Users: server/etcdserver/server.go:1087 (applySnapshot), before kv.Restore.
// Assumes: the caller is the writer; be2 is a new backend whose lease bucket holds exactly ids, which
// are distinct; rd is a deleter the caller has rdOk for (ReqRecoverRevoke: the server's closure).
// Specs: lessor.Recover.spec, lessor.Lookup.spec, lessor.Leases.spec, Lease.Keys.spec.
func ReqRecover(le lease.Lessor, be2 backend.Backend, rd lease.RangeDeleter, ids []lease.LeaseID) {
	le.Recover(be2, rd)
	for _, id := range ids {
		l := le.Lookup(id)
		if l == nil || len(l.Keys()) != 0 {
			panic("recover: a lease lost, or keys kept")
		}
	}
	if len(le.Leases()) != len(ids) {
		panic("recover: a lease not in the bucket")
	}
}

// REQ lease/expired-channel: what the expiry channel delivers are objects of leases the lessor
// granted (each with its ID readable); with the expiry mode off, nothing is delivered.
// Users: server/etcdserver/server.go:835-845 (run's expiry arm), 855 (revokeExpiredLeases).
// Assumes: granted holds every id the lessor ever had; expiry says whether the lessor was made
// with the expiry mode on (off: the deployment premise leasesOutliveRun).
// Specs: lessor.ExpiredLeasesC.spec; laws: expiredCh_recv, leaseObj_id, leaseObj_live.
func ReqExpiredChannel(le lease.Lessor, granted map[lease.LeaseID]bool, expiry bool) {
	ls := <-le.ExpiredLeasesC()
	if !expiry {
		panic("expired-channel: an expiry with the mode off")
	}
	for _, l := range ls {
		if !granted[l.ID] {
			panic("expired-channel: a lease never granted")
		}
	}
}

// REQ lease/stop: the lessor stops once (Cleanup), and its methods still answer after it.
// Users: server/etcdserver/server.go:947 (Cleanup).
// Assumes: Stop is called once (lessorStop).
// Specs: lessor.Stop.spec, lessor.Lookup.spec.
func ReqStop(le lease.Lessor, id lease.LeaseID) {
	le.Stop()
	_ = le.Lookup(id)
}

// REQ lease/grant-hook: a grant writes its bucket record under the batch lock with the backend's
// post-lock hook run (the apply thread's hook saves the consistent index with the record, 2d;
// examples/mvccrand checks it the same way).
// Users: server/etcdserver/apply/backend.go:84 (LeaseGrant on the apply thread, the hook of
// server.go:404); examples/mvccrand/mvccrand.go:503-504.
// Assumes: the caller is the writer; be is the lessor's backend and its hook is the one set here
// (beHook be Pk f with f this closure); id ≠ 0 not live; ttl ≤ MaxLeaseTTL.
// Specs: lessor.Grant.spec (Pre: ran = 0; Post: ran = 1), Lease.beHook, Lease.beHookRun.
func ReqGrantHook(le lease.Lessor, be backend.Backend, id lease.LeaseID, ttl int64) {
	var ran atomic.Int64
	be.SetTxPostLockInsideApplyHook(func() { ran.Add(1) })
	if _, err := le.Grant(id, ttl); err != nil {
		panic("grant-hook: grant refused")
	}
	if ran.Load() != 1 {
		panic("grant-hook: the post-lock hook did not run in the grant's lock")
	}
}

type noCluster struct{}

func (noCluster) Version() *semver.Version { return nil }

// REQ lease/new-lessor: a lessor over a backend whose bucket holds a lease (a restart) has it live,
// its TTL raised to the minimum, no key attached; it answers, and stops once.
// Users: server/etcdserver/server.go:344 (NewServer: the server's logger, backend, membership);
// examples/mvccrand/mvccrand.go:810 (zap.NewNop(), noCluster{}).
// Assumes: be's lease bucket holds exactly lease id with TTL ttl (beLeases); a real logger.
// Specs: NewLessor.spec (Zap.isLogger of NewNop's, clusterOk of noCluster: the transparent
// Version() triple, proved from its body; leaseRevokeRate 0; the caller's threadTok, given back:
// the run loop has its fork's own), lessor.Lookup.spec, Lease.TTL.spec, Lease.Keys.spec, lessor.Stop.spec; laws:
// lessorAt_minTTL.
func ReqNewLessor(be backend.Backend, id lease.LeaseID, ttl, minTTL int64) {
	le := lease.NewLessor(zap.NewNop(), be, noCluster{}, lease.LessorConfig{MinLeaseTTL: minTTL})
	l := le.Lookup(id)
	want := ttl
	if want < minTTL {
		want = minTTL
	}
	if l == nil || l.TTL() != want || len(l.Keys()) != 0 {
		panic("new-lessor: the bucket's lease not loaded")
	}
	le.Stop()
}

// REQ lease/promote-checkpointer: the server installs its checkpointer before it starts (the closure
// may be called only once the server started); the lessor calls it only when primary, after a
// Promote (on the apply thread, once started), with context.Background(), from a thread that may
// start a goroutine (the server's closure proposes through raftRequest: a thread token); Demote
// runs concurrently (the raft loop); Renew's errors stay the lessor's.
// Users: server/etcdserver/server.go:395-404 (SetCheckpointer in NewServer), 1990 (Promote), 769
// (Demote), v3_server.go:528 (Renew).
// Assumes: SetCheckpointer is called once (lessorCkptTok); started is set before Promote (the gate
// R: started's load is true); id was granted and never revoked nor recovered over; the caller
// holds a thread token (Renew lends it to the checkpointer).
// Specs: lessor.SetCheckpointer.spec (ckptOk cp R: at Background(), with the caller's threadTok),
// lessor.Promote.spec (ckptGate le R, □ R), lessor.Demote.spec, lessor.Renew.spec (the caller's
// threadTok lent to the checkpointer).
func ReqPromoteCheckpointer(le lease.Lessor, started *atomic.Bool, id lease.LeaseID) {
	le.SetCheckpointer(func(ctx context.Context, cp *pb.LeaseCheckpointRequest) error {
		if !started.Load() {
			panic("promote-checkpointer: the checkpointer called before the server started")
		}
		if ctx != context.Background() {
			panic("promote-checkpointer: the checkpointer called with another context")
		}
		done := make(chan struct{})
		go func() { close(done) }()
		<-done
		return nil
	})
	started.Store(true)
	le.Promote(0)
	done := make(chan struct{})
	go func() { le.Demote(); close(done) }()
	if _, err := le.Renew(id); err != nil && err != lease.ErrNotPrimary {
		panic("promote-checkpointer: an unexpected renewal error")
	}
	<-done
}

// REQ lease/recover-revoke: after a snapshot's Recover, the deleter is the server's closure over its
// KV store; a revocation then deletes the lease's keys through it as before.
// Users: server/etcdserver/server.go:1087 (applySnapshot's Recover), then apply/backend.go:95
// (LeaseRevoke).
// Assumes: the caller is the writer inside an apply; be2's bucket holds exactly id; kv is the
// server's KV store over be2 (its Restore done, key k carrying lease id, re-attached here); the
// server owes rdOk for its closure (2d: req/go_etcd_io_etcd_server_v3_etcdserver.md, "from 3c").
// Specs: lessor.Recover.spec, lessor.Attach.spec, lessor.Revoke.spec (rdOk of the closure),
// lessor.Lookup.spec, lessor.GetLease.spec.
func ReqRecoverRevoke(le lease.Lessor, be2 backend.Backend, kv mvcc.KV, id lease.LeaseID, k string) {
	le.Recover(be2, func() lease.TxnDelete { return kv.Write(traceutil.TODO()) })
	if err := le.Attach(id, []lease.LeaseItem{{Key: k}}); err != nil {
		panic("recover-revoke: the snapshot's lease not loaded")
	}
	if err := le.Revoke(id); err != nil {
		panic("recover-revoke: revoke refused")
	}
	if le.Lookup(id) != nil || le.GetLease(lease.LeaseItem{Key: k}) != lease.NoLease {
		panic("recover-revoke: lease or its key still live")
	}
}

// REQ lease/renew-forward: a follower forwards a keep-alive to the leader's peer URLs; it returns
// the TTL, or the lessor's ErrLeaseNotFound (errors.Is on any error RenewHTTP returns is safe), and
// retries every other error.
// Users: server/etcdserver/v3_server.go:551-555 (LeaseRenew's forwarding loop).
// Assumes: rt is the server's peer round tripper (rtOk); the caller holds a thread token.
// Specs: leasehttp.RenewHTTP.spec (nil, Lease.errIs ErrLeaseNotFound, or errIsNot), Lease.init.
func ReqRenewForward(ctx context.Context, id lease.LeaseID, urls []string, rt http.RoundTripper) (int64, error) {
	for _, u := range urls {
		ttl, err := leasehttp.RenewHTTP(ctx, id, u+leasehttp.LeasePrefix, rt)
		if err == nil || errors.Is(err, lease.ErrLeaseNotFound) {
			if err != nil && err != lease.ErrLeaseNotFound {
				panic("renew-forward: a not-found error that is not the lessor's")
			}
			return ttl, err
		}
	}
	return -1, ctx.Err()
}
