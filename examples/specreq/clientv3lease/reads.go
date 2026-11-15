package clientv3lease

import (
	"context"

	clientv3 "go.etcd.io/etcd/client/v3"
)

// REQ clientv3lease/ttl-about: TimeToLive answers about the lease asked for; an unknown lease is
// TTL -1 with GrantedTTL 0 and no keys (not an error).
// Users: examples/etcd/lease/leasekv.go:77-83 ("TimeToLive answered about another lease"),
// examples/etcd/leaseexpiry (TTL == -1 && GrantedTTL == 0: gone).
// Assumes: none.
// Specs: lessor.TimeToLive.spec (leaseTTLReply), WithAttachedKeys.spec (W0).
func ReqTimeToLiveAbout(ctx context.Context, cli *clientv3.Client, id clientv3.LeaseID) {
	t, err := cli.Lease.TimeToLive(ctx, id, clientv3.WithAttachedKeys())
	if err != nil {
		return
	}
	if t.ID != id {
		panic("ttl-about: answer about another lease")
	}
	if t.GrantedTTL == 0 && t.TTL == -1 && len(t.Keys) != 0 {
		panic("ttl-about: an unknown lease with keys")
	}
}

// REQ clientv3lease/leases-granted: every id Leases lists was granted at some point, and none is
// listed twice.
// Users: examples/etcd/lease/leasekv.go:63 (no id twice), examples/etcd/leasegrant (the granted
// id among them: needs the per-member lease views W0 left open, not asserted here).
// Assumes: the caller's invariant records every granted id (it sees every grant: Grant's update).
// Specs: lessor.Leases.spec (leaseLeasesReply); model: leaseStep's .leaseLeases.
func ReqLeasesNoDup(ctx context.Context, cli *clientv3.Client) {
	ls, err := cli.Lease.Leases(ctx)
	if err != nil {
		return
	}
	seen := map[clientv3.LeaseID]bool{}
	for _, l := range ls.Leases {
		if seen[l.ID] {
			panic("leases-granted: id listed twice")
		}
		seen[l.ID] = true
	}
}

// REQ clientv3lease/keepalive-once: KeepAliveOnce answers about the lease asked for: a positive
// TTL with no error, or ErrLeaseNotFound with a non-positive TTL, or an error and no response.
// Users: etcdctl (lease keep-alive --once); none in scope.
// Specs: lessor.KeepAliveOnce.spec.
func ReqKeepAliveOnce(ctx context.Context, cli *clientv3.Client, id clientv3.LeaseID) {
	r, err := cli.Lease.KeepAliveOnce(ctx, id)
	if err == nil {
		if r.ID != id || r.TTL <= 0 {
			panic("keepalive-once: bad success")
		}
		return
	}
	if r != nil && r.ID != id {
		panic("keepalive-once: response about another lease")
	}
}
