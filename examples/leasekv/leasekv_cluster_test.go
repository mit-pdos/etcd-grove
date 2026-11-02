package leasekv

import (
	"context"
	"net"
	"net/http"
	"testing"
	"time"

	"go.uber.org/zap"

	"go.etcd.io/etcd/client/pkg/v3/types"
	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/server/v3/etcdserver"
	"go.etcd.io/etcd/server/v3/lease/leasehttp"

	"github.com/mit-pdos/etcd-grove/examples/common"
)

// TestClusterLeaseReads tests, on a three-member cluster, the two facts the lease specs claim and
// Main's checks rest on (notes/lease-ex-plan.md, "Test"), on the paths Main's single member does not
// reach: TimeToLive's reply is about the asked lease (the leader answers from its lessor, a
// follower forwards to the leader over HTTP, leasehttp.TimeToLiveHTTP), for granted leases, with
// and without their keys, and for a missing one; Leases lists no lease twice, asked of every
// member, with leases granted through every member.
//
// The members' peer listeners serve what etcd's embed serves there (etcdhttp.NewPeerHandler): the
// raft handler and the lease handler. examples/common's NewMember serves only the raft handler, so
// in the examples a follower's TimeToLive gets the leader's mux 404, which TimeToLiveHTTP reads
// as lease.ErrLeaseNotFound: the reply is "TTL -1" for a lease that exists (its ID still the
// asked one).
func TestClusterLeaseReads(t *testing.T) {
	t.Chdir(t.TempDir())
	lg := zap.NewNop()
	peers := []string{"127.0.0.1:23951", "127.0.0.1:23952", "127.0.0.1:23953"}
	clients := []string{"127.0.0.1:23956", "127.0.0.1:23957", "127.0.0.1:23958"}
	names := []string{"leasekv3-1", "leasekv3-2", "leasekv3-3"}
	cluster := types.URLsMap{}
	for i, p := range peers {
		cluster[names[i]] = types.URLs{{Scheme: "http", Host: p}}
	}
	srvs := make([]*etcdserver.EtcdServer, 3)
	clis := make([]*clientv3.Client, 3)
	for i := range peers {
		s, err := common.NewServer(names[i], cluster[names[i]], clients[i], cluster, "leasekv3",
			common.NoSnapCount, common.NoSnapCatchUp, lg)
		if err != nil {
			t.Fatal(err)
		}
		l, err := net.Listen("tcp", peers[i])
		if err != nil {
			t.Fatal(err)
		}
		mux := http.NewServeMux()
		mux.Handle("/", s.RaftHandler())
		mux.Handle(leasehttp.LeasePrefix, s.LeaseHandler())
		mux.Handle(leasehttp.LeaseInternalPrefix, s.LeaseHandler())
		go http.Serve(l, mux)
		srvs[i] = s
	}
	for _, s := range srvs {
		s.Start()
	}
	for i, s := range srvs {
		if err := common.Serve(s, clients[i]); err != nil {
			t.Fatal(err)
		}
		cli, err := clientv3.New(clientv3.Config{Endpoints: []string{clients[i]}, Logger: lg})
		if err != nil {
			t.Fatal(err)
		}
		defer cli.Close()
		clis[i] = cli
	}
	ctx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
	defer cancel()

	// leases granted through every member, one with a key attached
	var ids []clientv3.LeaseID
	for r := 0; r < 4; r++ {
		for _, cli := range clis {
			g, err := cli.Grant(ctx, 600)
			if err != nil {
				t.Fatal(err)
			}
			ids = append(ids, g.ID)
		}
	}
	if _, err := clis[0].Put(ctx, "k", "v", clientv3.WithLease(ids[0])); err != nil {
		t.Fatal(err)
	}
	absent := clientv3.LeaseID(7)

	paths := map[bool]int{} // answers from the leader (true) and from followers (false)
	for i, cli := range clis {
		leader := srvs[i].Leader() == srvs[i].MemberID()
		for _, id := range append(ids, absent) {
			for _, keys := range []bool{false, true} {
				var opts []clientv3.LeaseOption
				if keys {
					opts = append(opts, clientv3.WithAttachedKeys())
				}
				ttl, err := cli.TimeToLive(ctx, id, opts...)
				if err != nil {
					t.Fatalf("member %d: TimeToLive(%x): %v", i, id, err)
				}
				if ttl.ID != id {
					t.Fatalf("member %d (leader %v): TimeToLive(%x) answered about %x", i, leader,
						id, ttl.ID)
				}
				if (id == absent) != (ttl.TTL == -1) {
					t.Fatalf("member %d (leader %v, keys %v): TimeToLive(%x): TTL %d", i, leader, keys,
						id, ttl.TTL)
				}
				paths[leader]++
			}
		}

		ls, err := cli.Leases(ctx)
		if err != nil {
			t.Fatalf("member %d: Leases: %v", i, err)
		}
		seen := map[clientv3.LeaseID]bool{}
		for _, l := range ls.Leases {
			if seen[l.ID] {
				t.Fatalf("member %d: Leases listed %x twice", i, l.ID)
			}
			seen[l.ID] = true
		}
		if len(ls.Leases) != len(ids) {
			t.Fatalf("member %d: Leases listed %d leases, %d granted", i, len(ls.Leases), len(ids))
		}
	}
	if paths[true] == 0 || paths[false] == 0 {
		t.Fatalf("not both paths exercised: leader %d, followers %d", paths[true], paths[false])
	}
	t.Logf("%d leases; TimeToLive answers: leader %d, followers %d", len(ids), paths[true],
		paths[false])
}
