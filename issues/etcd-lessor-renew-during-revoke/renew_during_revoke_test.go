// Reproduction of issues/etcd-lessor-renew-during-revoke.md.
//
// Package lease, file server/lease/renew_during_revoke_test.go of go.etcd.io/etcd (module
// go.etcd.io/etcd/server/v3), at the etcd pin of etc/goose.py: 107edf7e4 (branch goose-lean of
// upamanyus/etcd).
//
// Run, in server/:
//
//	GOTOOLCHAIN=go1.27.1 go test ./lease -run '^TestRenewDuringRevoke$' -count=1
//
// Fails at the pin (shows the bug): "Renew returned TTL 1 while Revoke was deleting the lease's
// keys; after Revoke, Lookup = <nil>".
package lease

import (
	"context"
	"testing"
	"time"

	"go.uber.org/zap"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/server/v3/storage/backend"
)

type blockingDeleter struct {
	tx         backend.BatchTx
	in, resume chan struct{}
}

func (d *blockingDeleter) DeleteRange(key, end []byte) (int64, int64) {
	d.in <- struct{}{}
	<-d.resume
	return 1, 0
}

func (d *blockingDeleter) End() { d.tx.Unlock() }

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
