// Package peerforge is the Go evidence for route B of the PeerServe_dist review (2026-11-25,
// notes/etcd-dist-plan.md §17.3): what an arbitrary peer request can do to a member, through the
// names-only leasehttp.RenewHTTP (which posts a LeaseKeepAliveRequest to any URL) and through the
// server's PromoteMember.
//
//   - (a) PromoteMember of an unknown id: refused before any proposal (isLearnerReady: the id is not
//     in raft's progress, ErrIDNotFound; no entry applied). Of a voter: isLearnerReady passes (its
//     match is the leader's), the leader proposes an AddNode{IsPromote} conf change, which apply
//     rejects (ValidateConfigurationChange: ErrMemberNotLearner): one entry applied, the members as
//     they were, no panic. The same through RenewHTTP to the peer URL's /members/promote/<id>.
//   - (b) RenewHTTP to the peer URL's /leases/internal: the body decodes as a LeaseInternalRequest
//     whose LeaseTimeToLiveRequest is nil (field 1 has the wrong wire type, kept as unknown), and the
//     handler dereferences it before any lock (lease/leasehttp/http.go); net/http's conn.serve
//     recovers the panic and closes the connection; the member keeps serving, its lessor usable.
package peerforge

import (
	"context"
	"net"
	"net/http"
	"strconv"
	"testing"
	"time"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/client/pkg/v3/types"
	"go.etcd.io/etcd/server/v3/etcdserver"
	"go.etcd.io/etcd/server/v3/etcdserver/api/etcdhttp"
	"go.etcd.io/etcd/server/v3/lease"
	"go.etcd.io/etcd/server/v3/lease/leasehttp"
	"go.uber.org/zap"

	"github.com/mit-pdos/etcd-grove/examples/lib/etcdstart"
	"github.com/mit-pdos/etcd-grove/examples/lib/walarea"
)

func members(s *etcdserver.EtcdServer) string {
	r := ""
	for _, m := range s.Cluster().Members() {
		r += m.ID.String() + " " + m.Name + " " + m.PeerURLs[0] + " learner=" + map[bool]string{true: "y", false: "n"}[m.IsLearner] + ";"
	}
	return r
}

func TestPeerForge(t *testing.T) {
	t.Chdir(t.TempDir())
	walarea.ResetFamily(t, "f")
	lg := zap.NewNop()
	l, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	peer := types.URLs{{Scheme: "http", Host: l.Addr().String()}}
	pu := peer[0].String()
	s, err := etcdstart.BuildServer("f-1", peer, "127.0.0.1:33899", types.URLsMap{"f-1": peer}, "f",
		etcdstart.NoSnapCount, etcdstart.NoSnapCatchUp, lg)
	if err != nil {
		t.Fatal(err)
	}
	s.Start()
	defer s.Stop()
	go http.Serve(l, etcdhttp.NewPeerHandler(lg, s))
	ctx := context.Background()
	for s.Leader() == 0 {
		time.Sleep(50 * time.Millisecond)
	}
	if _, err := s.Put(ctx, &pb.PutRequest{Key: []byte("k"), Value: []byte("v")}); err != nil {
		t.Fatal(err)
	}
	m0 := members(s)
	t.Logf("members: %s", m0)

	// (a) PromoteMember: an unknown id, then the voter itself
	for _, c := range []struct {
		id      uint64
		applied bool
	}{{777, false}, {uint64(s.MemberID()), true}} {
		id := c.id
		a0 := s.AppliedIndex()
		cctx, cancel := context.WithTimeout(ctx, 10*time.Second)
		_, err := s.PromoteMember(cctx, id)
		cancel()
		t.Logf("PromoteMember %x: %v (applied %d -> %d)", id, err, a0, s.AppliedIndex())
		if err == nil {
			t.Fatalf("promote %x: no error", id)
		}
		if (s.AppliedIndex() > a0) != c.applied {
			t.Fatalf("promote %x: applied %d -> %d, want an entry applied: %v", id, a0, s.AppliedIndex(), c.applied)
		}
		if m := members(s); m != m0 {
			t.Fatalf("members changed: %s -> %s", m0, m)
		}
	}

	rt := http.DefaultTransport
	// (a') the same through RenewHTTP to the peer URL's /members/promote/<id>
	for _, c := range []struct {
		path    string
		applied bool
	}{{"/members/promote/309", false}, {"/members/promote/" + strconv.FormatUint(uint64(s.MemberID()), 10), true}} {
		path := c.path
		a0 := s.AppliedIndex()
		cctx, cancel := context.WithTimeout(ctx, 10*time.Second)
		ttl, err := leasehttp.RenewHTTP(cctx, 1, pu+path, rt)
		cancel()
		t.Logf("RenewHTTP %s: %d %v (applied %d -> %d)", path, ttl, err, a0, s.AppliedIndex())
		if (s.AppliedIndex() > a0) != c.applied {
			t.Fatalf("%s: applied %d -> %d, want an entry applied: %v", path, a0, s.AppliedIndex(), c.applied)
		}
		if m := members(s); m != m0 {
			t.Fatalf("members changed: %s -> %s", m0, m)
		}
	}

	// (b) RenewHTTP to /leases/internal: the handler's nil dereference, recovered by conn.serve
	for i := 0; i < 3; i++ {
		cctx, cancel := context.WithTimeout(ctx, 10*time.Second)
		ttl, err := leasehttp.RenewHTTP(cctx, 5, pu+"/leases/internal", rt)
		cancel()
		t.Logf("RenewHTTP /leases/internal: %d %v", ttl, err)
		if err == nil {
			t.Fatal("no error")
		}
	}
	// the member still serves, its lessor usable (no lock left held)
	g, err := s.LeaseGrant(ctx, &pb.LeaseGrantRequest{TTL: 60})
	if err != nil {
		t.Fatal(err)
	}
	if _, err := s.LeaseRenew(ctx, lease.LeaseID(g.ID)); err != nil {
		t.Fatal(err)
	}
	if _, err := s.LeaseTimeToLive(ctx, &pb.LeaseTimeToLiveRequest{ID: g.ID, Keys: true}); err != nil {
		t.Fatal(err)
	}
	cctx, cancel := context.WithTimeout(ctx, 10*time.Second)
	ttl, err := leasehttp.RenewHTTP(cctx, lease.LeaseID(g.ID), pu+leasehttp.LeasePrefix, rt)
	cancel()
	if err != nil || ttl <= 0 {
		t.Fatalf("lease renew over HTTP after the panics: %d %v", ttl, err)
	}
	if r, err := s.Range(ctx, &pb.RangeRequest{Key: []byte("k")}); err != nil || len(r.Kvs) != 1 {
		t.Fatalf("range: %v", err)
	}
	if m := members(s); m != m0 {
		t.Fatalf("members changed: %s -> %s", m0, m)
	}
}
