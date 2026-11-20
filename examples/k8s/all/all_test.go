package k8sall

// These tests use the drivers' fixed ports and data directories (examples/k8s/etcd3,
// examples/k8s/compactor): do not run them at the same time as those packages' tests.

import (
	"context"
	"strconv"
	"testing"
	"time"

	"go.etcd.io/etcd/client/pkg/v3/types"
	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/server/v3/etcdserver/api/membership"
	"go.uber.org/zap"

	k8setcd3 "github.com/mit-pdos/etcd-grove/examples/k8s/etcd3"
	"github.com/mit-pdos/etcd-grove/examples/lib/cluster3"
	"github.com/mit-pdos/etcd-grove/examples/lib/etcdstart"
	"github.com/mit-pdos/etcd-grove/examples/lib/walarea"
)

// maxMembers is the bound of k8s_safe's member count k (the store's cluster).
const maxMembers = 1000

// The compactor's cluster (examples/k8s/compactor's clusterConfig, unexported there).
var compactorNames = []string{"k8scompactorp-1", "k8scompactorp-2", "k8scompactorp-3"}
var compactorPeers = []string{"127.0.0.1:23941", "127.0.0.1:23942", "127.0.0.1:23943"}
var compactorAddrs = []string{"127.0.0.1:23941", "127.0.0.1:23942", "127.0.0.1:23943",
	"127.0.0.1:23931", "127.0.0.1:23932", "127.0.0.1:23933",
	"127.0.0.1:23951", "127.0.0.1:23952", "127.0.0.1:23953"}

const compactorToken = "k8scompactorp"

// ids returns the member ids etcd computes (from the peer URLs and the token, as bootstrap does).
func ids(t *testing.T, names []string, peers []string, token string) []types.ID {
	urls := types.URLsMap{}
	for i := range names {
		u, err := types.NewURLs([]string{"http://" + peers[i]})
		if err != nil {
			t.Fatal(err)
		}
		urls[names[i]] = u
	}
	cl, err := membership.NewClusterFromURLsMap(zap.NewNop(), token, urls)
	if err != nil {
		t.Fatal(err)
	}
	return cl.MemberIDs()
}

// TestMemberIDs checks k8s_safe's premise Hlow: the 16 low bits of the ids of the process's every
// member (the store's k members and the compactor's three) are distinct and not 0, for every
// 1 <= k <= maxMembers. etcd's request-id generators carry them as their prefix, and the trusted
// model of idutil's Generator.Next assumes no two generators of the process issue one id.
func TestMemberIDs(t *testing.T) {
	comp := ids(t, compactorNames, compactorPeers, compactorToken)
	for k := uint64(1); k <= maxMembers; k++ {
		ms := etcdstart.Members("k8setcd3N", k, k8setcd3.PeerBase, k8setcd3.ClientBase)
		var names, peers []string
		for _, m := range ms {
			names = append(names, m.Name)
			peers = append(peers, m.Peer)
		}
		all := append(ids(t, names, peers, k8setcd3.Token), comp...)
		if uint64(len(all)) != k+3 {
			t.Fatalf("k=%d: %d ids", k, len(all))
		}
		seen := map[uint64]bool{}
		for _, id := range all {
			low := uint64(id) & 0xffff
			if low == 0 || seen[low] {
				t.Fatalf("k=%d: member %x: low 16 bits %#x zero or repeated", k, uint64(id), low)
			}
			seen[low] = true
		}
	}
}

// TestAddrs checks that the two clusters' addresses (the members' peer and client addresses and
// the bridges') and data directories are disjoint for every 1 <= k <= maxMembers.
func TestAddrs(t *testing.T) {
	for k := uint64(1); k <= maxMembers; k++ {
		seen := map[string]bool{}
		dirs := map[string]bool{}
		add := func(a string) {
			if seen[a] {
				t.Fatalf("k=%d: address %s twice", k, a)
			}
			seen[a] = true
		}
		for i, m := range etcdstart.Members("k8setcd3N", k, k8setcd3.PeerBase, k8setcd3.ClientBase) {
			add(m.Peer)
			add(m.Client)
			add("127.0.0.1:" + strconv.FormatUint(k8setcd3.BridgeBase+uint64(i), 10))
			dirs[walarea.DataDir(m.Name)] = true
		}
		for _, a := range compactorAddrs {
			add(a)
		}
		for _, n := range compactorNames {
			if dirs[walarea.DataDir(n)] {
				t.Fatalf("k=%d: data directory of %s twice", k, n)
			}
		}
	}
}

// TestMain runs Main at three members for the store with one schedule per cluster, the store's
// member 0 isolated and mended, the compactor's member 1 isolated and mended with member 2's
// bridge blackholed meanwhile: neither driver panics, and Main returns.
func TestMain(t *testing.T) {
	t.Chdir(t.TempDir())
	walarea.ResetFamily(t, "k8setcd3N", "k8scompactorp")
	ms := time.Millisecond
	cut := func(d time.Duration, k, m int, kind int) []cluster3.Step {
		var s []cluster3.Step
		for o := 0; o < k; o++ {
			if o != m {
				s = append(s, cluster3.Step{Delay: d, Kind: kind, A: m, B: o})
				d = 0
			}
		}
		return s
	}
	sched1 := append(cut(150*ms, 3, 0, cluster3.PeerCut), cut(300*ms, 3, 0, cluster3.PeerMend)...)
	sched2 := append(cut(150*ms, 3, 1, cluster3.PeerCut),
		cluster3.Step{Kind: cluster3.ClientBlackhole, A: 2})
	sched2 = append(sched2, cut(60*ms, 3, 1, cluster3.PeerMend)...)
	sched2 = append(sched2, cluster3.Step{Kind: cluster3.ClientUnblackhole, A: 2})
	start := time.Now()
	Main(3, 4, 60, 0, 0, sched1, sched2)
	t.Logf("Main took %v", time.Since(start))

	// both workloads ran: the store's revision moved past its seeds, and the compactors wrote
	// compact_rev_key
	for _, c := range []struct{ ep, key string }{
		{"127.0.0.1:21000", "/registry/objs/"}, {"127.0.0.1:23931", "compact_rev_key"}} {
		cli, err := etcdstart.NewClient(c.ep, zap.NewNop())
		if err != nil {
			t.Fatal(err)
		}
		ctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
		resp, err := cli.Get(ctx, c.key, clientv3.WithPrefix())
		cancel()
		cli.Close()
		if err != nil {
			t.Fatal(err)
		}
		t.Logf("%s at %s: %d keys, revision %d", c.key, c.ep, len(resp.Kvs), resp.Header.Revision)
		if len(resp.Kvs) == 0 || resp.Header.Revision < 10 {
			t.Fatalf("%s at %s: the workload did not run", c.key, c.ep)
		}
	}
}
