// Package leasegrant is the lease-grant example of etcd's server and client: one etcd member
// started in-process (as examples/leasekv starts it), a client connected to it, a lease granted
// through the client, then the client's listing of the leases: Main panics if the granted lease is
// not listed; the theorem to prove is that it does not (notes/lease-grant-plan.md), under the
// deployment premise that no lease granted in the run expires before the run ends (the TTL is 600
// seconds; the run takes seconds).
//
// Main calls only what the proofs specify: the examples' shared start (examples/common's
// StartServer, Serve and NewClient), the client's Grant and Leases (through its Lease field), each
// in a context with the examples' request timeout (context.WithTimeout of Background, cancelled
// after the call). An error from a step of the start, from the grant (a timeout, the connection, a
// server-chosen id that collides: ErrLeaseExists) or from the listing ends Main without a check: a
// call may fail, but a listing that answers must list the lease granted before it.
package leasegrant

import (
	"context"
	"time"

	"go.uber.org/zap"

	"github.com/mit-pdos/etcd-grove/examples/common"
)

// The client address (a plain host:port, clientv3.New's premise) and the peer address: not any
// other example's, so that the examples' tests can run at once.
const (
	clientAddr = "127.0.0.1:23956"
	peerAddr   = "127.0.0.1:23966"
)

// The TTL the lease is granted with, in seconds: far longer than the run.
const grantTTL = 600

// holdToken sleeps forever. Main runs it on a goroutine of its own, which touches no lock: the
// proof hands that goroutine's thread token to the gRPC server's one slot, for the goroutine grpc
// runs a call on (notes/lease-ex-plan.md, "The run's thread token").
func holdToken() {
	for {
		time.Sleep(time.Hour)
	}
}

// Main starts one member of a new cluster, connects a client, grants a lease and checks that the
// listing of the leases has it.
func Main() {
	lg := zap.NewNop()
	s, err := common.StartServer("leasegrant", peerAddr, clientAddr, lg)
	if err != nil {
		return
	}
	go holdToken()
	if err := common.Serve(s, clientAddr); err != nil {
		return
	}
	cli, err := common.NewClient(clientAddr, lg)
	if err != nil {
		return
	}
	gctx, gcancel := context.WithTimeout(context.Background(), common.RequestTimeout)
	g, err := cli.Lease.Grant(gctx, grantTTL)
	gcancel()
	if err != nil {
		return
	}

	lctx, lcancel := context.WithTimeout(context.Background(), common.RequestTimeout)
	ls, err := cli.Lease.Leases(lctx)
	lcancel()
	if err != nil {
		return
	}
	found := false
	for i := range ls.Leases {
		if ls.Leases[i].ID == g.ID {
			found = true
		}
	}
	if !found {
		panic("leasegrant: Leases did not list the lease granted")
	}
}
