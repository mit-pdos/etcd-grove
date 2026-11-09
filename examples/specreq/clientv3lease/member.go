package clientv3lease

import (
	"context"

	clientv3 "go.etcd.io/etcd/client/v3"
)

// REQ clientv3lease/grant-then-list-one-member: through a client of one endpoint (never changed), a
// lease granted and not revoked is listed by Leases.
// Users: examples/etcd/leasegrant/leasegrant.go:61-80 ("Leases did not list the lease granted"),
// examples/etcd/leasecatchup (member 3, caught up, lists the first lease).
// Assumes: cli is New's client of the single endpoint ep, auto-sync off, its endpoints token frozen
// (clientVia c ep: epsTok_persist); no principal revokes the lease and leases do not expire
// (EnvCfg.leaseExpiry = false, W0's K2).
// Specs: lessor.Grant.spec (Lease.GrantTriple with via = some ep: leaseViewLb γ ep of the table
// after the grant), lessor.Leases.spec (LeaseRead.Triple with via = some (ep, i): answered at a
// table j ≥ i, State.leaseAnsAt); laws: clientCore_leaseOf, leaseViewLb_le (W0); model: leaseStep.
func ReqGrantThenListOneMember(ctx context.Context, cli *clientv3.Client, ttl int64) {
	g, err := cli.Lease.Grant(ctx, ttl)
	if err != nil {
		return
	}
	ls, err := cli.Lease.Leases(ctx)
	if err != nil {
		return
	}
	for _, l := range ls.Leases {
		if l.ID == g.ID {
			return
		}
	}
	panic("grant-then-list-one-member: the granted lease is not listed")
}

// REQ clientv3lease/gone-not-listed: through a client of one endpoint, once Leases no longer lists a
// lease it granted, a later Leases does not list it either (the member's lessor only moves
// forward; unless the id is granted again).
// Users: examples/etcd/leaseexpiry/leaseexpiry.go:79-102 (there the expiry is seen by TimeToLive,
// which the leader answers: the same fact holds because its one member is the leader; a TimeToLive
// through a follower gives no per-member fact, re-review N1).
// Assumes: as above, and no principal grants the id again (the server chooses ids; the example
// grants one lease).
// Specs: lessor.Grant.spec (via: leaseViewLb γ ep of the table after the grant), lessor.Leases.spec
// (LeaseRead.Triple's view: an answer at ep's table j ≥ i gives leaseViewLb γ ep j); model:
// State.leaseAnsAt, leaseTables (a lease absent from a table after its grant is absent from every
// later one until granted again).
func ReqGoneNotListed(ctx context.Context, cli *clientv3.Client, ttl int64) {
	g, err := cli.Lease.Grant(ctx, ttl)
	if err != nil {
		return
	}
	listed := func() (bool, bool) {
		ls, err := cli.Lease.Leases(ctx)
		if err != nil {
			return false, false
		}
		for _, l := range ls.Leases {
			if l.ID == g.ID {
				return true, true
			}
		}
		return false, true
	}
	if in, ok := listed(); !ok || in {
		return
	}
	if in, ok := listed(); ok && in {
		panic("gone-not-listed: a lease no longer listed is listed again")
	}
}

// REQ clientv3lease/ttl-gone-not-listed-sole: in a single-member cluster, once TimeToLive reports a
// lease unknown, a later Leases does not list it (unless its id is granted again).
// Users: examples/etcd/leaseexpiry/leaseexpiry.go:79-102 ("Leases listed the lease after TimeToLive
// found it gone"; one member).
// Assumes: as above; the cluster has only ever had one member (soleMember γ, from ApiBoot's
// soleMember_intro: one initial member, no URL set reserved); no principal
// grants the id again.
// Specs: lessor.TimeToLive.spec, lessor.Leases.spec (LeaseRead.Triple's viaFact: TimeToLive's answer
// at ep's table i given soleMember; Leases answers at j ≥ i); model: State.leaseAnsAt.
func ReqTTLGoneNotListedSole(ctx context.Context, cli *clientv3.Client, id clientv3.LeaseID) {
	t, err := cli.Lease.TimeToLive(ctx, id)
	if err != nil || t.GrantedTTL != 0 {
		return
	}
	ls, err := cli.Lease.Leases(ctx)
	if err != nil {
		return
	}
	for _, l := range ls.Leases {
		if l.ID == id {
			panic("ttl-gone-not-listed-sole: a lease TimeToLive found gone is listed")
		}
	}
}
