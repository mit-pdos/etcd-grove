// Package leaseexpiry is the lease-expiry example of etcd's server and client: one etcd member
// started in-process (as examples/etcd/leasegrant starts it), a client connected to it, a lease of
// the shortest TTL granted through the client, then the client's TimeToLive polled until the
// member answers that the lease is not found (expired and revoked), then the client's listing of
// the leases: Main panics if the listing still has the lease; the theorem to prove is that it does
// not (notes/lease-expiry-plan.md), with no premise about time.
//
// Not found is TTL = -1 with GrantedTTL = 0: TTL = -1 alone is also the answer about a lease still
// in the lessor but overdue by a second or more (EtcdServer.LeaseTimeToLive answers
// int64(Remaining().Seconds()), and Remaining goes negative until the revocation is applied), which
// the listing still has.
//
// Main calls only what the proofs specify: the examples' shared start (examples/lib/etcdstart's
// StartServer, Serve and NewClient), the client's Grant, TimeToLive and Leases (through its Lease
// field), each in a context with the examples' request timeout, and time.Sleep between polls. An
// error from a step, or a lease not found within the polls, ends Main without a check: expiry is
// not promised by any deadline, but a listing after the not-found answer must not have the lease.
package leaseexpiry

import (
	"context"
	"time"

	"go.uber.org/zap"

	"github.com/mit-pdos/etcd-grove/examples/lib/etcdstart"
)

// The client address (a plain host:port, clientv3.New's premise) and the peer address: not any
// other example's, so that the examples' tests can run at once.
const (
	clientAddr = "127.0.0.1:23976"
	peerAddr   = "127.0.0.1:23986"
)

// grantTTL is below the member's minimum lease TTL (3/2 of the election timeout, rounded up to a
// second: 2 s at the start's 10 ticks of 100 ms), so the lessor grants the minimum.
const grantTTL = 1

// polls TimeToLive at most this often, pollEvery apart: about 20 s, against an expiry of about 3 s
// (the TTL, then the lessor's 500 ms expiry loop and the revocation through raft).
const (
	polls     = 80
	pollEvery = 250 * time.Millisecond
)

// holdToken is the run's thread token's goroutine (as in examples/etcd/leasegrant).
func holdToken() {
	for {
		time.Sleep(time.Hour)
	}
}

func Main() {
	lg := zap.NewNop()
	s, err := etcdstart.StartServer("leaseexpiry", peerAddr, clientAddr, lg)
	if err != nil {
		return
	}
	go holdToken()
	if err := etcdstart.Serve(s, clientAddr); err != nil {
		return
	}
	cli, err := etcdstart.NewClient(clientAddr, lg)
	if err != nil {
		return
	}
	gctx, gcancel := context.WithTimeout(context.Background(), etcdstart.RequestTimeout)
	g, err := cli.Lease.Grant(gctx, grantTTL)
	gcancel()
	if err != nil {
		return
	}

	gone := false
	for i := 0; i < polls && !gone; i++ {
		time.Sleep(pollEvery)
		tctx, tcancel := context.WithTimeout(context.Background(), etcdstart.RequestTimeout)
		t, err := cli.Lease.TimeToLive(tctx, g.ID)
		tcancel()
		if err != nil {
			return
		}
		if t.TTL == -1 && t.GrantedTTL == 0 {
			gone = true
		}
	}
	if !gone {
		return
	}

	lctx, lcancel := context.WithTimeout(context.Background(), etcdstart.RequestTimeout)
	ls, err := cli.Lease.Leases(lctx)
	lcancel()
	if err != nil {
		return
	}
	for i := range ls.Leases {
		if ls.Leases[i].ID == g.ID {
			panic("leaseexpiry: Leases listed the lease after TimeToLive found it gone")
		}
	}
}
