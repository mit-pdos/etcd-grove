// Package leasekv is the lease example of etcd's server and client: one etcd member started
// in-process (as examples/watchkv starts it), a client connected to it, and the client's two lease
// reads: Main panics if Leases lists a lease id twice or if TimeToLive's answer is about another
// lease than the one asked; the theorem to prove is that it does not (notes/lease-ex-plan.md). The
// checks hold whatever the lessor holds (the member holds no lease: no request the server's
// verified proposers send grants one; the test also checks the answers after a grant).
//
// Main calls only what the proofs specify: the examples' shared start (examples/common's
// StartServer, Serve and NewClient), the client's Leases and TimeToLive (through its Lease field),
// each in a context with the examples' request timeout (context.WithTimeout of Background,
// cancelled after the call). An error from a step of the start, or from either read, ends Main
// without a check: a read may fail (a timeout, the connection), but one that answers must answer as
// checked.
package leasekv

import (
	"context"

	"go.uber.org/zap"

	clientv3 "go.etcd.io/etcd/client/v3"

	"github.com/mit-pdos/etcd-grove/examples/common"
)

// The client address (a plain host:port, clientv3.New's premise) and the peer address: not any
// other example's, so that the examples' tests can run at once.
const (
	clientAddr = "127.0.0.1:23936"
	peerAddr   = "127.0.0.1:23946"
)

// The lease id TimeToLive asks about: any id, since the member holds no lease.
const leaseID = clientv3.LeaseID(7)

// Main starts one member of a new cluster, connects a client, and checks its two lease reads.
func Main() {
	lg := zap.NewNop()
	s, err := common.StartServer("leasekv", peerAddr, clientAddr, lg)
	if err != nil {
		return
	}
	if err := common.Serve(s, clientAddr); err != nil {
		return
	}
	cli, err := common.NewClient(clientAddr, lg)
	if err != nil {
		return
	}
	lctx, lcancel := context.WithTimeout(context.Background(), common.RequestTimeout)
	ls, err := cli.Lease.Leases(lctx)
	lcancel()
	if err != nil {
		return
	}
	for i := range ls.Leases {
		for j := 0; j < i; j++ {
			if ls.Leases[i].ID == ls.Leases[j].ID {
				panic("leasekv: Leases listed a lease twice")
			}
		}
	}

	tctx, tcancel := context.WithTimeout(context.Background(), common.RequestTimeout)
	ttl, err := cli.Lease.TimeToLive(tctx, leaseID)
	tcancel()
	if err != nil {
		return
	}
	if ttl.ID != leaseID {
		panic("leasekv: TimeToLive answered about another lease")
	}
}
