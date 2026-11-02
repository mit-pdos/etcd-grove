// Package leasekv is the lease example of etcd's server and client: one etcd member started
// in-process (as examples/watchkv starts it), a client connected to it, and the client's two lease
// reads: Main panics if Leases lists a lease id twice or if TimeToLive's answer is about another
// lease than the one asked; the theorem to prove is that it does not (notes/lease-ex-plan.md). The
// checks hold whatever the lessor holds (the member holds no lease: no request the server's
// verified proposers send grants one; the test also checks the answers after a grant).
//
// Main calls only what the proofs specify: the examples' shared start (examples/common's
// StartServer, Serve and NewClient), the client's Leases and TimeToLive (through its embedded
// Lease field) and context.Background. An error from a step of the start, or from either read,
// ends Main with Failed: a read may fail (a timeout, the connection), but one that answers must
// answer as checked.
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

// Main's results: the checks passed, or a step of the start or a read failed.
const (
	Ok     = 0
	Failed = 1
)

// Main starts one member of a new cluster, connects a client, and checks its two lease reads.
func Main() int {
	lg := zap.NewNop()
	s, err := common.StartServer("leasekv", peerAddr, clientAddr, lg)
	if err != nil {
		return Failed
	}
	if err := common.Serve(s, clientAddr); err != nil {
		return Failed
	}
	cli, err := common.NewClient(clientAddr, lg)
	if err != nil {
		return Failed
	}
	ctx := context.Background()

	ls, err := cli.Lease.Leases(ctx)
	if err != nil {
		return Failed
	}
	for i := range ls.Leases {
		for j := 0; j < i; j++ {
			if ls.Leases[i].ID == ls.Leases[j].ID {
				panic("leasekv: Leases listed a lease twice")
			}
		}
	}

	ttl, err := cli.Lease.TimeToLive(ctx, leaseID)
	if err != nil {
		return Failed
	}
	if ttl.ID != leaseID {
		panic("leasekv: TimeToLive answered about another lease")
	}
	return Ok
}
