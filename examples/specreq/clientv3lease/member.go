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

// REQ clientv3lease/gone-not-listed: through a client of one endpoint, once TimeToLive reports a
// lease unknown, a later Leases does not list it (unless its id is granted again).
// Users: examples/etcd/leaseexpiry/leaseexpiry.go:79-102 ("Leases listed the lease after TimeToLive
// found it gone").
// Assumes: as above, and no principal grants the id again (the server chooses ids; the example
// grants one lease).
// Specs: lessor.TimeToLive.spec, lessor.Leases.spec (LeaseRead.Triple's view: TimeToLive's answer
// at table i gives leaseViewLb γ ep i; Leases answers at j ≥ i); model: State.leaseAnsAt (a revoked
// lease is absent from every later table until granted again).
func ReqGoneNotListed(ctx context.Context, cli *clientv3.Client, id clientv3.LeaseID) {
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
			panic("gone-not-listed: a lease TimeToLive found gone is listed")
		}
	}
}
