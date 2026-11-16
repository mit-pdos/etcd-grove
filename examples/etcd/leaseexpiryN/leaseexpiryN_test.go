package leaseexpiryN

import (
	"context"
	"math/rand"
	"os"
	"strconv"
	"testing"
	"time"

	"go.etcd.io/etcd/client/pkg/v3/types"
	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/server/v3/etcdserver"
	"go.etcd.io/etcd/server/v3/etcdserver/api/membership"
	"go.uber.org/zap"

	"github.com/mit-pdos/etcd-grove/examples/lib/etcdstart"
)

// maxMembers is the bound of etcd_leaseexpiryN_safe's member count.
const maxMembers = 1000

// The address ranges of the tests that start a cluster of their own (k <= 7 members): not Main's,
// nor another example's.
const (
	naivePeerBase   uint64 = 14000
	naiveClientBase uint64 = 14100
	runPeerBase     uint64 = 14200
	runClientBase   uint64 = 14300
)

// idsOf returns the member ids etcd computes for the cluster of k members named pfx at the bases
// (from the peer URLs and the token, as bootstrap does), without starting it.
func idsOf(t *testing.T, pfx string, k uint64, peerBase uint64, clientBase uint64) []types.ID {
	ms := etcdstart.Members(pfx, k, peerBase, clientBase)
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

// TestMemberIDs checks etcd_leaseexpiryN_safe's premises on the member ids for every member count
// 1 <= k <= maxMembers, from the ids etcd computes for Main(k)'s cluster (the members' order is
// irrelevant to both): their 16 low bits distinct and not 0 (putgetN's BootFacts), and their 15
// low bits distinct (leaseIdsApart). It starts no cluster.
func TestMemberIDs(t *testing.T) {
	for k := uint64(1); k <= maxMembers; k++ {
		ids := idsOf(t, "leaseexpiryN", k, PeerBase, ClientBase)
		if uint64(len(ids)) != k {
			t.Fatalf("k=%d: %d ids", k, len(ids))
		}
		seen16 := map[uint64]bool{}
		seen15 := map[uint64]bool{}
		for _, id := range ids {
			low := uint64(id) & 0xffff
			if low == 0 || seen16[low] {
				t.Fatalf("k=%d: member %x: low 16 bits %#x zero or repeated", k, uint64(id), low)
			}
			seen16[low] = true
			l15 := uint64(id) & 0x7fff
			if seen15[l15] {
				t.Fatalf("k=%d: member %x: low 15 bits %#x repeated", k, uint64(id), l15)
			}
			seen15[l15] = true
		}
	}
}

// TestMembers checks Main's members' names and addresses at k = 3, and that Main(0) returns.
func TestMembers(t *testing.T) {
	ms := etcdstart.Members("leaseexpiryN", 3, PeerBase, ClientBase)
	want := []etcdstart.Member{
		{Name: "leaseexpiryN-0", Peer: "127.0.0.1:12000", Client: "127.0.0.1:13000"},
		{Name: "leaseexpiryN-1", Peer: "127.0.0.1:12001", Client: "127.0.0.1:13001"},
		{Name: "leaseexpiryN-2", Peer: "127.0.0.1:12002", Client: "127.0.0.1:13002"},
	}
	for i := range want {
		if ms[i] != want[i] {
			t.Fatalf("member %d: got %v, want %v", i, ms[i], want[i])
		}
	}
	Main(0)
}

// memberCount is the tests' k: drawn at random from {1, 2, 3, 5, 7} (LEASEEXPIRYN_MEMBERS=<k>
// overrides it), logged first so that a failure can be rerun.
func memberCount(t *testing.T) uint64 {
	ks := []uint64{1, 2, 3, 5, 7}
	k := ks[rand.Intn(len(ks))]
	if s := os.Getenv("LEASEEXPIRYN_MEMBERS"); s != "" {
		v, err := strconv.ParseUint(s, 10, 64)
		if err != nil || v < 1 || v > maxMembers {
			t.Fatalf("LEASEEXPIRYN_MEMBERS=%q: not a member count in 1..%d", s, maxMembers)
		}
		k = v
	}
	t.Logf("k=%d (rerun with LEASEEXPIRYN_MEMBERS=%d)", k, k)
	return k
}

// TestMainRun runs Main(k) for real, in a fresh directory (the members' DataDirs are relative).
// Main must not panic. Then, on the members Main left running: every member answers at its client
// address (Main served it), the cluster has k members, and no member lists a lease (every lease
// Main granted expired at every member); and a lease granted now through each member carries that
// member id's 15 low bits in its bits 48-62 (why the token must make them distinct).
func TestMainRun(t *testing.T) {
	k := memberCount(t)
	t.Chdir(t.TempDir())
	start := time.Now()
	Main(k)
	t.Logf("Main returned after %v", time.Since(start))

	ms := etcdstart.Members("leaseexpiryN", k, PeerBase, ClientBase)
	clis := make([]*clientv3.Client, len(ms))
	for j, m := range ms {
		cli, err := clientv3.New(clientv3.Config{Endpoints: []string{m.Client}, Logger: zap.NewNop()})
		if err != nil {
			t.Fatal(err)
		}
		defer cli.Close()
		clis[j] = cli
	}
	ctx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
	defer cancel()
	for j, m := range ms {
		ml, err := clis[j].MemberList(ctx)
		if err != nil || uint64(len(ml.Members)) != k {
			t.Fatalf("%s: MemberList: %v %v (want %d members; Main did not serve it?)", m.Name, ml,
				err, k)
		}
		ls, err := clis[j].Leases(ctx)
		if err != nil || len(ls.Leases) != 0 {
			t.Fatalf("%s: Leases after Main: %v %v (want none)", m.Name, ls.Leases, err)
		}
	}
	for j, m := range ms {
		st, err := clis[j].Status(ctx, m.Client)
		if err != nil {
			t.Fatal(err)
		}
		g, err := clis[j].Grant(ctx, 600)
		if err != nil {
			t.Fatal(err)
		}
		if got, want := (uint64(g.ID)>>48)&0x7fff, st.Header.MemberId&0x7fff; got != want {
			t.Fatalf("%s: lease %x: bits 48-62 %#x, member id's 15 low bits %#x", m.Name,
				uint64(g.ID), got, want)
		}
	}
}

// startCluster starts k members named pfx at the bases, with Main's token and start, in the
// current directory, and returns them. They are left running, as Main leaves its members: stopping
// a member whose peer listener still serves its raft handler makes the handler panic on the next
// message ("raft: stopped", recovered and logged by net/http: rafthttp's pipeline handler panics on
// every Process error, notes/specs-only/crashreconf-test.md), noise in the test's log.
func startCluster(t *testing.T, pfx string, k uint64, peerBase uint64,
	clientBase uint64) ([]*etcdserver.EtcdServer, []etcdstart.Member) {
	ms := etcdstart.Members(pfx, k, peerBase, clientBase)
	srvs, err := etcdstart.StartMembers(ms, Token, etcdstart.NoSnapCount, etcdstart.NoSnapCatchUp,
		zap.NewNop())
	if err != nil {
		t.Fatal(err)
	}
	return srvs, ms
}

// TestRunChecked runs run on a cluster of its own (Main's start, other ports) and requires its
// result Checked: every member's listing dropped the lease granted through it within the polls,
// so Main's checks are reached, not skipped on a timeout.
func TestRunChecked(t *testing.T) {
	k := memberCount(t)
	t.Chdir(t.TempDir())
	srvs, ms := startCluster(t, "leaseexpiryN-run", k, runPeerBase, runClientBase)
	start := time.Now()
	if r := run(srvs, ms, zap.NewNop()); r != Checked {
		t.Fatalf("run: %d, want Checked", r)
	}
	t.Logf("run checked %d members in %v", k, time.Since(start))
}

// TestTTLThroughFollowerPanics shows why leaseexpiryN reads "gone" off the member's listing and not
// off TimeToLive, as the one-member example does: on 3 members started as Main starts them, a lease
// granted through a follower is live (the follower lists it), yet the follower's TimeToLive answers
// "not found" (TTL -1, GrantedTTL 0): it forwards to the leader's peer URL, whose listener serves
// only the raft handler, and reads the 404 as ErrLeaseNotFound (leasehttp.TimeToLiveHTTP). The one
// member example's Main, run through that follower, would see the lease gone on its first poll,
// then find it listed, and panic.
func TestTTLThroughFollowerPanics(t *testing.T) {
	t.Chdir(t.TempDir())
	srvs, ms := startCluster(t, "leaseexpiryN-naive", 3, naivePeerBase, naiveClientBase)
	for j, m := range ms {
		if err := etcdstart.Serve(srvs[j], m.Client); err != nil {
			t.Fatal(err)
		}
	}
	f := -1
	for d := time.Now().Add(20 * time.Second); time.Now().Before(d) && f < 0; time.Sleep(50 * time.Millisecond) {
		for j, s := range srvs {
			if s.Leader() != 0 && s.Leader() != s.MemberID() {
				f = j
				break
			}
		}
	}
	if f < 0 {
		t.Fatal("no follower with a leader")
	}
	cli, err := etcdstart.NewClient(ms[f].Client, zap.NewNop())
	if err != nil {
		t.Fatal(err)
	}
	defer cli.Close()
	ctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
	defer cancel()
	g, err := cli.Grant(ctx, 60)
	if err != nil {
		t.Fatal(err)
	}
	ttl, err := cli.TimeToLive(ctx, g.ID)
	if err != nil {
		t.Fatal(err)
	}
	if ttl.TTL != -1 || ttl.GrantedTTL != 0 {
		t.Fatalf("follower's TimeToLive of a live lease: TTL %d, GrantedTTL %d (want the not-found "+
			"answer; if the examples' peers now serve leases, update leaseexpiryN's comment)", ttl.TTL,
			ttl.GrantedTTL)
	}
	ls, err := cli.Leases(ctx)
	if err != nil {
		t.Fatal(err)
	}
	if !listed(ls, g.ID) {
		t.Fatal("the follower does not list the lease granted through it")
	}
	t.Logf("member %d (a follower): TimeToLive says lease %x not found, yet lists it", f, int64(g.ID))
}
