// Package clientv3lease holds the requirement snippets of etcd's Go client lease API (batch 1c,
// Spec/go_etcd_io/etcd/client/v3/ApiLease.lean): minimal uses of the patterns its users rely on
// (client/v3/concurrency's Session, Kubernetes' lease manager, leasing and recipes through
// sessions, this repository's examples/etcd/lease*), each reliance an explicit panic.
//
// Common assumptions (the proofs' setting): cli is a client of a cluster (isClient), the caller
// owns the cluster's state etcdState in an invariant of its own; contexts carry no auth token
// metadata of their own (ctxPrin). Time is not modelled: a lease may expire at any moment (an
// environment step, EnvCfg.leaseExpiry), and a keep-alive says nothing about its liveness.
package clientv3lease

import (
	"context"

	"go.etcd.io/etcd/api/v3/v3rpc/rpctypes"
	clientv3 "go.etcd.io/etcd/client/v3"
)

// REQ clientv3lease/grant-ttl: a granted lease has a non-zero id and at least the TTL asked.
// Users: client/v3/concurrency/session.go:50 (resp.ID becomes the session's lease),
// Kubernetes' lease_manager.go:109 (lcr.ID attached to event keys), examples/etcd/leasegrant.
// Assumes: 0 < ttl <= MaxLeaseTTL.
// Specs: lessor.Grant.spec (Lease.methods' Grant: CallTriple with a persistent update,
// leaseGrantReply); model: leaseStep's .leaseGrant (id' != 0, ttl <= ttl').
func ReqGrantTTL(ctx context.Context, cli *clientv3.Client, ttl int64) {
	resp, err := cli.Lease.Grant(ctx, ttl)
	if err != nil {
		return
	}
	if resp.ID == clientv3.NoLease {
		panic("grant-ttl: lease id 0")
	}
	if resp.TTL < ttl {
		panic("grant-ttl: granted TTL below the asked one")
	}
}

// REQ clientv3lease/grant-then-put: a put with a just-granted lease is applied with that lease, or
// fails with ErrLeaseNotFound only if the lease expired meanwhile (an environment step the
// caller's invariant sees), never with another definite error than the model's.
// Users: client/v3/concurrency/mutex.go (the waiter's key with the session lease),
// election.go (Campaign), Kubernetes' store (events with a TTL lease), leasing.
// Assumes: k is owned (no other writer). Grant's update may fire more than once (a resent grant):
// each firing is a lease granted; the Q Grant returns is the last firing's, whose id the put uses.
// Specs: lessor.Grant.spec, Client.Put.spec (W0), WithLease.spec (W0); model: kvStep's put
// (PutReq.check: lease live).
func ReqGrantThenPut(ctx context.Context, cli *clientv3.Client, k, v string, ttl int64) {
	g, err := cli.Lease.Grant(ctx, ttl)
	if err != nil {
		return
	}
	_, err = cli.Put(ctx, k, v, clientv3.WithLease(g.ID))
	if err != nil && err != rpctypes.ErrLeaseNotFound {
		// any other error is indefinite or a refusal: retried by the callers
		return
	}
	if err == nil {
		gr, err := cli.Get(ctx, k)
		if err != nil {
			return
		}
		// the key may be gone (the lease expired after the put), never with another lease
		if len(gr.Kvs) == 1 && gr.Kvs[0].Lease != int64(g.ID) {
			panic("grant-then-put: key attached to another lease")
		}
	}
}
