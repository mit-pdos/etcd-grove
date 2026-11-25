// Package leaseexpiryN is the lease-expiry example (examples/etcd/leaseexpiry) for any number k of
// members (notes/leaseN-plan.md): the k members of a new cluster started in-process with the
// examples' generic start (etcdstart.Members, etcdstart.StartMembers, as examples/etcd/putgetN
// starts them), each serving its raft handler on its own peer listener and etcd's gRPC API on its
// own client address; through a client of each member, a lease of the shortest TTL granted (so k
// leases, one through every member); then, at every member in turn, the member's listing of the
// leases polled until it no longer lists the lease granted through it (expired: the leader's lessor
// revoked it through raft, and the member applied the revocation), then listed once more: Main
// panics if that listing has the lease again; the theorem to prove (etcd_leaseexpiryN_safe) is that
// it does not, for every member count 1 <= k <= 1000, with no premise about time.
//
// Unlike the one-member example, "gone" is read off the member's own listing, not off TimeToLive:
// a member that is not the leader forwards TimeToLive to the leader's peer URL, which the examples'
// members do not serve for leases (their peer listeners serve the raft handler only), and reads the
// 404 as "lease not found" while the lease is live; so the one-member example's check, run through
// a follower, panics (TestTTLThroughFollowerPanics). A member's listing reads its own lessor, which
// holds the lease from the grant's apply (the member that proposed the grant applied it before
// answering) until it applies the revocation, and never again: the member's lessor grants an id
// once (the members' lease ids are apart: their member ids' 15 low bits are distinct at the token,
// TestMemberIDs).
//
// Main calls only what the proofs specify: the generic start, etcdstart's Serve and NewClient, the
// clients' Grant and Leases (through their Lease field), each in a context with the examples'
// request timeout, and time.Sleep between polls. An error from a step, or a lease still listed
// after the polls, ends Main without the checks that follow: expiry is not promised by any
// deadline, but a listing after one without the lease must not have it.
package leaseexpiryN

import (
	"context"
	"time"

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
	PeerBase   uint64 = 12000
	ClientBase uint64 = 13000
)

// Token is the cluster's token (etcd's --initial-cluster-token), from which, with its peer URL,
// etcd computes each member's id: the first leaseexpiryN-<n> whose first 1000 members' ids have
// distinct nonzero 16 low bits (putgetN's BootFacts) and distinct 15 low bits (leaseIdsApart: a
// lease id carries only 15 bits of its member's id, so two members agreeing there could generate
// the same lease id, issues/etcd-lease-id-mask-member-prefix.md); TestMemberIDs checks both.
const Token = "leaseexpiryN-1973196"

// grantTTL is below the members' minimum lease TTL (3/2 of the election timeout, rounded up to a
// second: 2 s at the start's 10 ticks of 100 ms), so the lessor grants the minimum.
const grantTTL = 1

// A member's listing is polled at most this often, pollEvery apart: about 20 s, against an expiry
// of about 3 s (the TTL, then the leader's 500 ms expiry loop and the revocation through raft).
const (
	polls     = 80
	pollEvery = 250 * time.Millisecond
)

// run's results: every member's check ran; a step failed, or a lease stayed listed, before the
// checks ended.
const (
	Checked = 0
	Failed  = 1
)

// grant grants a lease of TTL grantTTL through cli, in a context with the request timeout.
func grant(cli *clientv3.Client) (*clientv3.LeaseGrantResponse, error) {
	ctx, cancel := context.WithTimeout(context.Background(), etcdstart.RequestTimeout)
	g, err := cli.Lease.Grant(ctx, grantTTL)
	cancel()
	return g, err
}

// leases lists the leases of cli's member, in a context with the request timeout.
func leases(cli *clientv3.Client) (*clientv3.LeaseLeasesResponse, error) {
	ctx, cancel := context.WithTimeout(context.Background(), etcdstart.RequestTimeout)
	ls, err := cli.Lease.Leases(ctx)
	cancel()
	return ls, err
}

// listed says whether the listing ls has the lease id.
func listed(ls *clientv3.LeaseLeasesResponse, id clientv3.LeaseID) bool {
	found := false
	for i := range ls.Leases {
		if ls.Leases[i].ID == id {
			found = true
		}
	}
	return found
}

// gone polls cli's member's listing until it does not list id, and reports whether it saw that
// within the polls (false also on a listing's error).
func gone(cli *clientv3.Client, id clientv3.LeaseID) bool {
	for i := 0; i < polls; i++ {
		time.Sleep(pollEvery)
		ls, err := leases(cli)
		if err != nil {
			return false
		}
		if !listed(ls, id) {
			return true
		}
	}
	return false
}

// run serves every started member's gRPC API at its client address, grants a lease through a
// client of each member, then, member by member, waits until the member no longer lists the lease
// granted through it and checks that its next listing does not have it either.
func run(srvs []*etcdserver.EtcdServer, ms []etcdstart.Member, lg *zap.Logger) int {
	for j, m := range ms {
		if err := etcdstart.Serve(srvs[j], m.Client); err != nil {
			return Failed
		}
	}
	clis := make([]*clientv3.Client, len(ms))
	ids := make([]clientv3.LeaseID, len(ms))
	for j, m := range ms {
		cli, err := etcdstart.NewClient(m.Client, lg)
		if err != nil {
			return Failed
		}
		g, err := grant(cli)
		if err != nil {
			return Failed
		}
		clis[j] = cli
		ids[j] = g.ID
	}
	for j := range ms {
		if !gone(clis[j], ids[j]) {
			return Failed
		}
		ls, err := leases(clis[j])
		if err != nil {
			return Failed
		}
		if listed(ls, ids[j]) {
			panic("leaseexpiryN: a member listed an expired lease again")
		}
	}
	return Checked
}

// Main starts the k members of a new cluster and checks, at each member, that the lease granted
// through it, once expired, is no longer listed (run).
func Main(k uint64) {
	if k < 1 || k > 1000 { // the cluster sizes the proof covers; any other k runs nothing
		return
	}
	lg := zap.NewNop()
	ms := etcdstart.Members("leaseexpiryN", k, PeerBase, ClientBase)
	srvs, err := etcdstart.StartMembers(ms, Token, etcdstart.NoSnapCount, etcdstart.NoSnapCatchUp,
		lg)
	if err != nil {
		return
	}
	run(srvs, ms, lg)
}
