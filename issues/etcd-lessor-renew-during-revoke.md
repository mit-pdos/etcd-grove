---
upstream: known
checked: 2026-10-16
links:
  - etcd-io/etcd#14758 issue closed: the user report (keys of a kept-alive lease gone); closed as not reproducible; this race is the one concrete candidate, not a confirmed diagnosis
  - etcd-io/etcd#21389 pr closed: same race and fix (close revokec under le.mu at Revoke's start, check it in Renew), with a failpoint integration test; closed unmerged by the stale bot
  - etcd-io/etcd#13915 issue closed: related, not this bug (leases not linearizable, the API reporting a lease gone by its TTL before raft revokes it)
---

# lease: `Renew` succeeds while `Revoke` is deleting the lease's keys

- **Status**: a bug (a wrong result: a keep-alive answers "alive for TTL seconds" for a lease whose
  revocation is being applied; the lease and its keys are gone right after).
- **Where**: `server/lease/lessor.go` at the pinned revision (`etc/goose.py`, `107edf7e4`):
  `lessor.Renew` (`:396`) checks `l.expired()` (`:415`) after dropping `le.mu.RLock`, may wait in
  the checkpointer `le.cp` (`:437`, a raft proposal in the server), then re-checks only that the
  lease is still in `leaseMap` (`:442-448`) and refreshes it (`:449`). `lessor.Revoke` (`:326`) drops
  `le.mu` (`:337`) to delete the lease's keys (`:350`) and removes the lease from `leaseMap` only
  after them (`:355`); `revokec` is closed when `Revoke` returns (`defer close(l.revokec)`, `:335`).
  `Renew`'s documentation: "If the given lease does not exist or has expired, an error will be
  returned."
- **What happens**: a `Renew` that passed its expiry check just before the lease expired, then
  waited, takes `le.mu` while the expiry `Revoke` is deleting the keys, finds the lease and returns a
  positive TTL. Reproduction (a unit test in `server/lease`,
  `issues/etcd-lessor-renew-during-revoke/renew_during_revoke_test.go`; fails deterministically at
  the pin, go1.27.2: "Renew returned TTL 1 while Revoke was deleting the lease's keys; after Revoke,
  Lookup = <nil>"). Its test function (`blockingDeleter` is in the file):

  ```go
  func TestRenewDuringRevoke(t *testing.T) {
  	_, be := NewTestBackend(t)
  	defer be.Close()

  	le := newLessor(zap.NewNop(), be, clusterLatest(), LessorConfig{MinLeaseTTL: 1})
  	defer le.Stop()

  	cpIn, cpGo := make(chan struct{}), make(chan struct{})
  	le.SetCheckpointer(func(ctx context.Context, cp *pb.LeaseCheckpointRequest) error {
  		cpIn <- struct{}{}
  		<-cpGo
  		return nil
  	})
  	d := &blockingDeleter{in: make(chan struct{}), resume: make(chan struct{})}
  	le.SetRangeDeleter(func() TxnDelete {
  		d.tx = be.BatchTx()
  		d.tx.Lock()
  		return d
  	})
  	le.Promote(0)

  	l, err := le.Grant(1, 1)
  	if err != nil {
  		t.Fatal(err)
  	}
  	if err := le.Attach(l.ID, []LeaseItem{{Key: "foo"}}); err != nil {
  		t.Fatal(err)
  	}
  	// a checkpointed remaining TTL, so that Renew clears it through the checkpointer
  	le.mu.Lock()
  	l.remainingTTL = 1
  	le.mu.Unlock()

  	type res struct {
  		ttl int64
  		err error
  	}
  	renewc := make(chan res, 1)
  	go func() {
  		ttl, err := le.Renew(l.ID)
  		renewc <- res{ttl, err}
  	}()
  	<-cpIn // Renew passed its expiry check, the lease not expired yet

  	for !l.expired() {
  		time.Sleep(10 * time.Millisecond)
  	}
  	revokec := make(chan error, 1)
  	go func() { revokec <- le.Revoke(l.ID) }() // the expiry revocation, applied
  	<-d.in                                       // Revoke is deleting the lease's keys

  	close(cpGo)
  	r := <-renewc
  	close(d.resume)
  	if err := <-revokec; err != nil {
  		t.Fatal(err)
  	}
  	if r.err == nil && r.ttl > 0 {
  		t.Errorf("Renew returned TTL %d while Revoke was deleting the lease's keys; after Revoke, Lookup = %v", r.ttl, le.Lookup(l.ID))
  	}
  }
  ```

  In the server the wait is real: with `LeaseCheckpoint` on, `Renew` clears a checkpointed TTL
  through a raft proposal; without it, only scheduling separates the two critical sections. #21389
  reproduces it end to end with failpoints.
- **Expected**: a `Renew` that returns a positive TTL is ordered before the revocation: no
  revocation of the lease has started when it refreshes the lease (`ErrLeaseNotFound` otherwise).
- **How the proof handles it**: outside it. `Renew` is names-only and `Revoke` translated but
  unproved (`notes/decisions.md`, "The lessor's apply-side methods (unit 9)": `Revoke`'s five
  obstacles); the apply package's `isApplyLessor` `Revoke` clause, a premise of
  `lessor_apply_contract`, is atomic for the store but says nothing of `Renew`. The TTL promise
  itself is a timing property the model has no clock for (`decisions.md`, "Leases without
  liveness"). Triage: `notes/bug-triage/etcd-14758.md`.
- **Possible fixes**: #21389's (close `revokec` under `le.mu` at the start of `Revoke`; in `Renew`,
  under `le.mu`, return `ErrLeaseNotFound` if it is closed; `Renew`'s first `select` on `revokec`
  then fires early, which is what it waits for anyway); or remove the lease from `leaseMap` before
  dropping the lock in `Revoke`.
- **Found**: 2026-10-16, bug triage of etcd-io/etcd#14758 (reproduced at the pin).
