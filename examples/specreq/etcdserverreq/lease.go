package etcdserverreq

import (
	"context"
	"errors"

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
// Users: server.go:882 (revokeExpiredLeases, one goroutine per lease, attached: it runs through
// HardStop until run's s.wg.Wait(), so it holds no srvGate share).
// Assumes: the update is built from envUpd (EnvStep.leaseExpire; the identity aborted); ctx has no
// incoming metadata or peer (s.ctx: ctxNoIncoming); the caller holds a thread token (GoAttach's).
// Specs: EtcdServer.AuthStore.spec, 3d's WithRoot spec, EtcdServer.LeaseRevoke.spec (no gate:
// verify round); laws: reqPrin_noIncoming (the context unchanged), reqPrin_root (the root token),
// and reqCtxOk of rctx (3d's WithRoot post giving rctx as a value-child of ctx: requested).
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

// REQ etcdserverreq/keepalive-follower: on a follower, a keep-alive is forwarded to the leader
// (leasehttp.RenewHTTP to its peer URLs); a not-found answer comes back as lease's
// ErrLeaseNotFound (definite: the client stops), any other forwarding error is retried until the
// request timeout (ErrTimeout, ErrCanceled: indefinite).
// Users: api/v3rpc/lease.go:136 on a member that is not the leader (every follower serving a
// keep-alive stream).
// Assumes: s is started and not the leader; the caller holds a gate share and a thread token.
// Specs: EtcdServer.LeaseRenew.spec (its forwarding path: waitLeader.spec, 3c's RenewHTTP post);
// laws: leaseErr_srv (ErrLeaseNotFound is the server sentinel of leaseNotFound), srvErr_leaf.
func ReqKeepAliveFollower(ctx context.Context, s *etcdserver.EtcdServer, id int64) (int64, bool) {
	ttl, err := s.LeaseRenew(ctx, lease.LeaseID(id))
	if errors.Is(err, lease.ErrLeaseNotFound) {
		return 0, false // definite: the lease is gone
	}
	if err != nil {
		return -1, true // indefinite: the client retries
	}
	return ttl, true
}

// REQ etcdserverreq/lease-reply-header: a lease method's success reply carries a header (the gRPC
// handler fills it: hdr.fill panics on a nil one).
// Users: api/v3rpc/lease.go:45,54,63,79 (hdr.fill(resp.Header) after LeaseGrant, LeaseRevoke,
// LeaseTimeToLive, LeaseLeases).
// Specs: EtcdServer.LeaseGrant.spec, EtcdServer.LeaseLeases.spec (srvHdrReply); law:
// replyHdrOwn_header (verify round, A6-provability F1).
func ReqLeaseReplyHeader(ctx context.Context, s *etcdserver.EtcdServer, ttl int64) uint64 {
	g, err := s.LeaseGrant(ctx, &pb.LeaseGrantRequest{TTL: ttl})
	if err != nil {
		return 0
	}
	ls, err := s.LeaseLeases(ctx, &pb.LeaseLeasesRequest{})
	if err != nil {
		return g.Header.MemberId
	}
	return g.Header.MemberId + ls.Header.MemberId
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
