package leaseN

import (
	"context"
	"math/rand"
	"os"
	"strconv"
	"testing"
	"time"

	"go.etcd.io/etcd/client/pkg/v3/types"
	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/server/v3/etcdserver/api/membership"
	"go.uber.org/zap"

	"github.com/mit-pdos/etcd-grove/examples/lib/etcdstart"
	"github.com/mit-pdos/etcd-grove/examples/lib/walarea"
)

// maxMembers is the bound of etcd_leaseN_safe's member count.
const maxMembers = 1000

// idsOf returns the member ids etcd computes for Main(k)'s cluster (from the peer URLs and the
// cluster token, as bootstrap does), without starting it.
func idsOf(t *testing.T, k uint64) []types.ID {
	ms := etcdstart.Members("leaseN", k, PeerBase, ClientBase)
	urls := types.URLsMap{}
	for _, m := range ms {
		u, err := types.NewURLs([]string{"http://" + m.Peer})
		if err != nil {
			t.Fatal(err)
		}
		urls[m.Name] = u
	}
	cl, err := membership.NewClusterFromURLsMap(zap.NewNop(), Token, urls)
	if err != nil {
		t.Fatal(err)
	}
	return cl.MemberIDs()
}

// TestMemberIDs checks etcd_leaseN_safe's premise on the member ids (putgetN's BootFacts: their 16
// low bits distinct and not 0) for every member count 1 <= k <= maxMembers, from the ids etcd
// computes for Main(k)'s cluster. It starts no cluster.
func TestMemberIDs(t *testing.T) {
	for k := uint64(1); k <= maxMembers; k++ {
		ids := idsOf(t, k)
		if uint64(len(ids)) != k {
			t.Fatalf("k=%d: %d ids", k, len(ids))
		}
		seen := map[uint64]bool{}
		for _, id := range ids {
			low := uint64(id) & 0xffff
			if low == 0 || seen[low] {
				t.Fatalf("k=%d: member %x: low 16 bits %#x zero or repeated", k, uint64(id), low)
			}
			seen[low] = true
		}
	}
}

// TestMembers checks Main's members' names and addresses at k = 3, and that Main(0) returns.
func TestMembers(t *testing.T) {
	ms := etcdstart.Members("leaseN", 3, PeerBase, ClientBase)
	want := []etcdstart.Member{
		{Name: "leaseN-0", Peer: "127.0.0.1:10000", Client: "127.0.0.1:11000"},
		{Name: "leaseN-1", Peer: "127.0.0.1:10001", Client: "127.0.0.1:11001"},
		{Name: "leaseN-2", Peer: "127.0.0.1:10002", Client: "127.0.0.1:11002"},
	}
	for i := range want {
		if ms[i] != want[i] {
			t.Fatalf("member %d: got %v, want %v", i, ms[i], want[i])
		}
	}
	Main(0)
}

// TestMainRun runs Main(k) for real, in a fresh directory (the members' DataDirs are relative),
// for one member count k drawn at random from {1, 2, 3, 5, 7} (LEASEN_MEMBERS=<k> overrides it),
// logged first so that a failure can be rerun. Main must not panic. Then, on the members Main left
// running, the test checks that Main got past its serve loop (every member answers at its client
// address), that the cluster has k members and a leader, and that every member's reads answer as
// Main's checks require: an empty listing (no member holds a lease), and TimeToLive about the
// lease asked, not found (a follower's forwarded call too: the leader's peer listener answers 404).
func TestMainRun(t *testing.T) {
	ks := []uint64{1, 2, 3, 5, 7}
	k := ks[rand.Intn(len(ks))]
	if s := os.Getenv("LEASEN_MEMBERS"); s != "" {
		v, err := strconv.ParseUint(s, 10, 64)
		if err != nil || v < 1 || v > maxMembers {
			t.Fatalf("LEASEN_MEMBERS=%q: not a member count in 1..%d", s, maxMembers)
		}
		k = v
	}
	t.Logf("leaseN: k=%d (rerun with LEASEN_MEMBERS=%d)", k, k)
	t.Chdir(t.TempDir())
	walarea.ResetFamily(t, "leaseN") // the members' WAL areas (wal-link P2)
	start := time.Now()
	Main(k)
	t.Logf("Main returned after %v", time.Since(start))

	ms := etcdstart.Members("leaseN", k, PeerBase, ClientBase)
	leaders := map[uint64]bool{}
	for _, m := range ms {
		cli, err := clientv3.New(clientv3.Config{Endpoints: []string{m.Client}, Logger: zap.NewNop()})
		if err != nil {
			t.Fatal(err)
		}
		ctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
		st, err := cli.Status(ctx, m.Client)
		if err != nil {
			t.Fatalf("%s: Status: %v (Main did not serve it?)", m.Name, err)
		}
		leaders[st.Leader] = true
		ml, err := cli.MemberList(ctx)
		if err != nil || uint64(len(ml.Members)) != k {
			t.Fatalf("%s: MemberList: %v %v (want %d members)", m.Name, ml, err, k)
		}
		ls, err := cli.Leases(ctx)
		if err != nil || len(ls.Leases) != 0 {
			t.Fatalf("%s: Leases: %v %v (want none)", m.Name, ls, err)
		}
		ttl, err := cli.TimeToLive(ctx, leaseID)
		if err != nil || ttl.ID != leaseID || ttl.TTL != -1 {
			t.Fatalf("%s: TimeToLive(%d): %v %v (want not found, about %d)", m.Name, leaseID, ttl,
				err, leaseID)
		}
		cancel()
		cli.Close()
	}
	if len(leaders) != 1 || leaders[0] {
		t.Fatalf("members' leaders: %v (want one, not 0)", leaders)
	}
}
