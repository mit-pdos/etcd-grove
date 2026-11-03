package leasegrant

import (
	"context"
	"net"
	"net/http"
	"testing"
	"time"

	"go.uber.org/zap"
	"google.golang.org/grpc/status"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/api/v3/v3rpc/rpctypes"
	"go.etcd.io/etcd/client/pkg/v3/types"
	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/server/v3/etcdserver"
	"go.etcd.io/etcd/server/v3/lease"
	"go.etcd.io/etcd/server/v3/lease/leasehttp"

	"github.com/mit-pdos/etcd-grove/examples/common"
)

// TestClusterLeaseGrant tests, on a three-member cluster, the facts the lease-grant specs claim
// (Proof/go_etcd_io/etcd/client/v3/InvLeaseGrant.lean) on the paths Main's single member does not
// reach: grants proposed by a follower as well as by the leader, listings asked of followers, and
// grants that fail at the apply.
//
//   - etcdLeaseGrantSpec: a grant through any member (a client with that member's endpoint only)
//     answers with an ID other than NoLease (0) and a header revision etcd has reached (> 0: a new
//     cluster's revision is 1).
//   - etcdLeaseLeasesSpec: the listing is member-local (EtcdServer.LeaseLeases reads the member's
//     own lessor, no read index), and the spec promises a member lists only the grants granted at
//     its own lessor; a grant's reply comes after the answering member applied it (raftRequest
//     waits for the member's own apply), so Leases asked of member X lists every grant X answered,
//     checked right after each grant and again at the end, for grants made through every member;
//     no member lists a lease twice. A member is not checked for the grants other members answered
//     (it may lag).
//   - Amendment (E) of notes/lease-grant-plan.md: a grant that fails at the apply fails with the
//     lessor's error, never ErrNoSpace. clientv3's Grant cannot choose the ID, so these go through
//     the raw etcdserverpb.LeaseClient on the client's connection: an ID already granted (through
//     another member than the one asked, so the duplicate entry is proposed by a member that did
//     not answer the first grant; it is applied after the first, the log being one order) fails
//     with ErrGRPCLeaseExist, a TTL over lease.MaxLeaseTTL with ErrGRPCLeaseTTLTooLarge. Both
//     checks are at the apply (lessor.Grant), not before the proposal: EtcdServer.LeaseGrant
//     checks neither, and v3rpc's togRPCError maps the lessor's errors to the gRPC ones. Neither
//     failed grant is listed afterwards.
//
// The peer listeners serve the raft and lease handlers, as in examples/leasekv's
// TestClusterLeaseReads; the ports differ from it and from Main's, so the tests can run at once.
func TestClusterLeaseGrant(t *testing.T) {
	t.Chdir(t.TempDir())
	lg := zap.NewNop()
	peers := []string{"127.0.0.1:23961", "127.0.0.1:23962", "127.0.0.1:23963"}
	clients := []string{"127.0.0.1:23967", "127.0.0.1:23968", "127.0.0.1:23969"}
	names := []string{"leasegrant3-1", "leasegrant3-2", "leasegrant3-3"}
	cluster := types.URLsMap{}
	for i, p := range peers {
		cluster[names[i]] = types.URLs{{Scheme: "http", Host: p}}
	}
	srvs := make([]*etcdserver.EtcdServer, 3)
	clis := make([]*clientv3.Client, 3)
	for i := range peers {
		s, err := common.BuildServer(names[i], cluster[names[i]], clients[i], cluster, "leasegrant3",
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

	// listed returns member i's listing as a set, failing on a lease listed twice.
	listed := func(i int) map[clientv3.LeaseID]bool {
		ls, err := clis[i].Leases(ctx)
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
		return seen
	}

	// grants through every member; each listed by its member right after
	answered := make([][]clientv3.LeaseID, 3) // the grants member i answered
	paths := map[bool]int{}                   // grants answered by the leader (true), followers (false)
	for r := 0; r < 4; r++ {
		for i, cli := range clis {
			g, err := cli.Grant(ctx, 600)
			if err != nil {
				t.Fatalf("member %d: Grant: %v", i, err)
			}
			if g.ID == clientv3.NoLease {
				t.Fatalf("member %d: Grant answered NoLease", i)
			}
			if g.ResponseHeader == nil || g.ResponseHeader.Revision <= 0 {
				t.Fatalf("member %d: Grant's header %v", i, g.ResponseHeader)
			}
			if !listed(i)[g.ID] {
				t.Fatalf("member %d: Leases right after the grant does not list %x", i, g.ID)
			}
			answered[i] = append(answered[i], g.ID)
			paths[srvs[i].Leader() == srvs[i].MemberID()]++
		}
	}
	if paths[true] == 0 || paths[false] == 0 {
		t.Fatalf("not both paths exercised: leader %d, followers %d", paths[true], paths[false])
	}

	// failures: the lessor's error, never ErrNoSpace
	isErr := func(err, want error) bool {
		got, w := status.Convert(err), status.Convert(want)
		return got.Code() == w.Code() && got.Message() == w.Message()
	}
	const tooLargeID = 0x7e57
	for i, cli := range clis {
		lc := pb.NewLeaseClient(cli.ActiveConnection())
		dup := answered[(i+1)%3][0] // granted through another member
		_, err := lc.LeaseGrant(ctx, &pb.LeaseGrantRequest{TTL: 600, ID: int64(dup)})
		if err == nil || isErr(err, rpctypes.ErrGRPCNoSpace) || !isErr(err, rpctypes.ErrGRPCLeaseExist) {
			t.Fatalf("member %d: grant of the existing %x: %v, want %v", i, dup, err,
				rpctypes.ErrGRPCLeaseExist)
		}
		_, err = lc.LeaseGrant(ctx, &pb.LeaseGrantRequest{TTL: lease.MaxLeaseTTL + 1, ID: tooLargeID})
		if err == nil || isErr(err, rpctypes.ErrGRPCNoSpace) ||
			!isErr(err, rpctypes.ErrGRPCLeaseTTLTooLarge) {
			t.Fatalf("member %d: grant with TTL %d: %v, want %v", i, lease.MaxLeaseTTL+1, err,
				rpctypes.ErrGRPCLeaseTTLTooLarge)
		}
	}

	// every member lists the grants it answered, no lease twice, and not the failed grant
	for i := range clis {
		seen := listed(i)
		for _, id := range answered[i] {
			if !seen[id] {
				t.Fatalf("member %d: Leases does not list %x, which it granted", i, id)
			}
		}
		if seen[tooLargeID] {
			t.Fatalf("member %d: Leases lists the grant that failed (TTL too large)", i)
		}
	}
	t.Logf("grants answered: leader %d, followers %d", paths[true], paths[false])
}
