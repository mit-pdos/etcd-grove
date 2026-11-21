// Package leaseN is the lease example (examples/etcd/lease) for any number k of members
// (notes/leaseN-plan.md): the k members of a new cluster started in-process with the examples'
// generic start (etcdstart.Members, etcdstart.StartMembers, as examples/etcd/putgetN starts them),
// each serving its raft handler on its own peer listener and etcd's gRPC API on its own client
// address; then, at every member in turn, through a client of that member, the lease example's two
// reads: Main panics if a member's Leases lists a lease id twice or if its TimeToLive answers about
// another lease than the one asked; the theorem to prove (etcd_leaseN_safe) is that it does not,
// for every member count 1 <= k <= 1000.
//
// As in the lease example, the cluster grants no lease (no request Main sends grants one), so the
// checks hold whatever each member's lessor holds. At a member that is not the leader, TimeToLive
// is forwarded to the leader's peer URL (leasehttp.TimeToLiveHTTP), which the examples' members do
// not serve for leases (their peer listeners serve the raft handler only): the leader's 404 reads
// as "lease not found", answered with the asked id; the check is on that id, which the forwarded
// path checks too (EtcdServer.leaseTimeToLive's spec).
//
// Main calls only what the proofs specify: the generic start, etcdstart's Serve and NewClient, the
// clients' Leases and TimeToLive (through their Lease field), each in a context with the examples'
// request timeout (context.WithTimeout of Background, cancelled after the call). An error from a
// step ends Main without the checks that follow it: a read may fail, but one that answers must
// answer as checked.
package leaseN

import (
	"context"

	"go.uber.org/zap"

	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/server/v3/etcdserver"

	"github.com/mit-pdos/etcd-grove/examples/lib/etcdstart"
)

// The members' address ranges: member i's peer address is 127.0.0.1:(PeerBase+i) (its one peer
// URL http://<addr>, served by its raft handler), its client address 127.0.0.1:(ClientBase+i)
// (served by its gRPC API): ranges no other example uses, so that the examples' tests can run at
// once; for k <= 1000 the two ranges are disjoint and every port is at most 65535.
const (
	PeerBase   uint64 = 10000
	ClientBase uint64 = 11000
)

// Token is the cluster's token (etcd's --initial-cluster-token), from which, with its peer URL,
// etcd computes each member's id: the first leaseN-<n> whose first 300 members' ids have distinct
// nonzero 16 low bits, also from the ids of examples/etcd/all's other clusters (putgetN's BootFacts,
// etcd_safe's Hlow; TestMemberIDs here and there). Above 300 members the ids are not checked:
// etcd_leaseN_safe's premise on them may be false there. The cluster grants no lease, so the
// ids' 15 low bits need not be distinct.
const Token = "leaseN-1302"

// The lease id TimeToLive asks about: any id, since no member holds a lease.
const leaseID = clientv3.LeaseID(7)

// run's results: every member's reads were checked; a step failed before the checks ended.
const (
	Checked = 0
	Failed  = 1
)

// check makes the lease example's two reads through a new client of the member at addr and
// panics if either answers wrongly; it reports whether both answered.
func check(addr string, lg *zap.Logger) bool {
	cli, err := etcdstart.NewClient(addr, lg)
	if err != nil {
		return false
	}
	lctx, lcancel := context.WithTimeout(context.Background(), etcdstart.RequestTimeout)
	ls, err := cli.Lease.Leases(lctx)
	lcancel()
	if err != nil {
		return false
	}
	for i := range ls.Leases {
		for j := 0; j < i; j++ {
			if ls.Leases[i].ID == ls.Leases[j].ID {
				panic("leaseN: Leases listed a lease twice")
			}
		}
	}

	tctx, tcancel := context.WithTimeout(context.Background(), etcdstart.RequestTimeout)
	ttl, err := cli.Lease.TimeToLive(tctx, leaseID)
	tcancel()
	if err != nil {
		return false
	}
	if ttl.ID != leaseID {
		panic("leaseN: TimeToLive answered about another lease")
	}
	return true
}

// run serves every started member's gRPC API at its client address, then checks every member's
// lease reads, in the members' order.
func run(srvs []*etcdserver.EtcdServer, ms []etcdstart.Member, lg *zap.Logger) int {
	for j, m := range ms {
		if err := etcdstart.Serve(srvs[j], m.Client); err != nil {
			return Failed
		}
	}
	for _, m := range ms {
		if !check(m.Client, lg) {
			return Failed
		}
	}
	return Checked
}

// Main starts the k members of a new cluster and checks each member's lease reads (run).
func Main(k uint64) {
	lg := zap.NewNop()
	ms := etcdstart.Members("leaseN", k, PeerBase, ClientBase)
	srvs, err := etcdstart.StartMembers(ms, Token, etcdstart.NoSnapCount, etcdstart.NoSnapCatchUp,
		lg)
	if err != nil {
		return
	}
	run(srvs, ms, lg)
}
