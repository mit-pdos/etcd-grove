// Package leasekv is the lease example of etcd's server and client: one etcd member started
// in-process (as examples/watchkv starts it), a client connected to it, and the client's two lease
// reads against the member's lessor, which holds no lease (no request the server's verified
// proposers send grants one): Main panics unless Leases lists no lease and TimeToLive of a lease id
// answers TTL -1, the server's answer for a lease it does not hold; the theorem to prove is that
// it does not (notes/lease-ex-plan.md).
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
	if len(ls.Leases) != 0 {
		panic("leasekv: Leases listed a lease")
	}

	ttl, err := cli.Lease.TimeToLive(ctx, leaseID)
	if err != nil {
		return Failed
	}
	if ttl.TTL != -1 {
		panic("leasekv: TimeToLive of a lease the member does not hold")
	}
	return Ok
}
