// Requirement snippets for server/lease, the lessor (batch 3c): what the apply thread (3a's
// applier, 3b's txn, 3e's mvcc, 2d's applySnapshot), the request path (2c) and the server's
// lifecycle (2d, 2e) rely on.
package lease

import (
	"go.etcd.io/etcd/server/v3/lease"
	"go.etcd.io/etcd/server/v3/storage/backend"
)

// REQ lease/grant-lookup: a grant of a non-zero id that is not live, with a TTL at most
// MaxLeaseTTL, succeeds; the lease is then live with its object's ID and a TTL raised to the
// minimum; a second grant of it is ErrLeaseExists, a grant of id 0 ErrLeaseNotFound, a TTL above
// MaxLeaseTTL ErrLeaseTTLTooLarge.
// Users: server/etcdserver/apply/backend.go:84 (LeaseGrant: l.ID, l.TTL()), txn/put.go:83 and
// apply/auth.go:199 (Lookup at the writer), v3_server.go:652 (TTL()).
// Assumes: the caller is the lessor's writer (lessorState) inside an apply (beApplyTok); id ≠ 0 is
// not live; ttl ≤ MaxLeaseTTL; the lessor was made with MinLeaseTTL minTTL.
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
// Assumes: the leases live are exactly ids (distinct), and nothing grants or revokes meanwhile.
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
// Assumes: the lease is never revoked; done carries the grant's happening (lessorLb).
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
// Assumes: the caller is the writer; be2 is a new backend whose lease bucket holds exactly ids;
// rd is the KV store's deleter.
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
