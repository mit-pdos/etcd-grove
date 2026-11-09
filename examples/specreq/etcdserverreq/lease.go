package etcdserverreq

import (
	"context"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/server/v3/etcdserver"
	"go.etcd.io/etcd/server/v3/lease"
)

// REQ etcdserverreq/grant-then-revoke: a granted lease has a non-zero id and a TTL at least the one
// asked; revoking it succeeds unless it expired meanwhile (ErrLeaseNotFound).
// Users: api/v3rpc/lease.go:45,54 (the client's Grant and Revoke; concurrency's Session).
// Assumes: ttl ≤ MaxLeaseTTL; no other principal revokes the leases this caller grants.
// Specs: EtcdServer.LeaseGrant.spec, EtcdServer.LeaseRevoke.spec; laws: replyOwn's (3h).
func ReqGrantThenRevoke(ctx context.Context, s *etcdserver.EtcdServer, ttl int64) {
	g, err := s.LeaseGrant(ctx, &pb.LeaseGrantRequest{TTL: ttl})
	if err != nil {
		return
	}
	if g.ID == 0 || g.TTL < ttl {
		panic("grant: bad id or ttl")
	}
	_, err = s.LeaseRevoke(ctx, &pb.LeaseRevokeRequest{ID: g.ID})
	_ = err // nil, ErrLeaseNotFound (expired), or another error: all handled by the caller
}

// REQ etcdserverreq/expiry-revoke: the lessor's revocation of an expired lease, with the root
// context, never panics (it ignores the reply).
// Users: server.go:882 (revokeExpiredLeases, one goroutine per lease).
// Assumes: the update is built from envUpd (EnvStep.leaseExpire; the identity aborted).
// Specs: EtcdServer.LeaseRevoke.spec; reqPrin_noIncoming of ctx (s.ctx: ctxNoIncoming), and 3d's
// WithRoot spec: reqPrin rctx (some root) none with auth enabled at the call, the context unchanged
// otherwise.
func ReqExpiryRevoke(ctx context.Context, s *etcdserver.EtcdServer, id int64) {
	rctx := s.AuthStore().WithRoot(ctx)
	_, _ = s.LeaseRevoke(rctx, &pb.LeaseRevokeRequest{ID: id})
}

// REQ etcdserverreq/keepalive: a keep-alive returns a TTL or an error, never panics; an
// ErrLeaseNotFound answer is definite (the client ends the keep-alive).
// Users: api/v3rpc/lease.go:136 (the keep-alive stream's loop).
// Specs: EtcdServer.LeaseRenew.spec.
func ReqKeepAlive(ctx context.Context, s *etcdserver.EtcdServer, id int64) int64 {
	ttl, err := s.LeaseRenew(ctx, lease.LeaseID(id))
	if err != nil {
		return -1
	}
	return ttl
}

// REQ etcdserverreq/time-to-live: a time-to-live answer names a lease that was granted, with the
// keys asked for.
// Users: api/v3rpc/lease.go:63 (the client's TimeToLive with WithAttachedKeys).
// Assumes: id was granted by this caller earlier (so ErrLeaseNotFound means it expired).
// Specs: EtcdServer.LeaseTimeToLive.spec.
func ReqTimeToLive(ctx context.Context, s *etcdserver.EtcdServer, id int64) {
	resp, err := s.LeaseTimeToLive(ctx, &pb.LeaseTimeToLiveRequest{ID: id, Keys: true})
	if err != nil {
		return
	}
	if resp.ID != id {
		panic("time-to-live: another lease")
	}
}

// REQ etcdserverreq/leases: the leases listed are distinct.
// Users: api/v3rpc/lease.go:79 (the client's Leases).
// Specs: EtcdServer.LeaseLeases.spec.
func ReqLeases(ctx context.Context, s *etcdserver.EtcdServer) {
	resp, err := s.LeaseLeases(ctx, &pb.LeaseLeasesRequest{})
	if err != nil {
		return
	}
	seen := map[int64]bool{}
	for _, l := range resp.Leases {
		if seen[l.ID] {
			panic("leases: duplicate id")
		}
		seen[l.ID] = true
	}
}
