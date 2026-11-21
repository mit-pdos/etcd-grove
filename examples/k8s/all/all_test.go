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

	"github.com/mit-pdos/etcd-grove/examples/k8s/compactor"
	k8setcd3 "github.com/mit-pdos/etcd-grove/examples/k8s/etcd3"
	"github.com/mit-pdos/etcd-grove/examples/lib/cluster3"
	"github.com/mit-pdos/etcd-grove/examples/lib/etcdstart"
	"github.com/mit-pdos/etcd-grove/examples/lib/walarea"
)

// maxMembers1 and maxMembers2 are the bounds of k8s_safe's member counts k1 (the store's cluster)
// and k2 (the compactor's).
const (
	maxMembers1 = 1000
	maxMembers2 = 600
)

// members returns the names and peer addresses of the first k members of the store's (etcd3) or the
// compactor's cluster.
func members(k uint64, compactorCluster bool) ([]string, []string) {
	var ms []etcdstart.Member
	if compactorCluster {
		ms = etcdstart.Members("k8scompactorN", k, compactor.PeerBase, compactor.ClientBase)
	} else {
		ms = etcdstart.Members("k8setcd3N", k, k8setcd3.PeerBase, k8setcd3.ClientBase)
	}
	var names, peers []string
	for _, m := range ms {
		names = append(names, m.Name)
		peers = append(peers, m.Peer)
	}
	return names, peers
}

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
// member (the store's k1 members and the compactor's k2) are distinct and not 0, for every
// 1 <= k1 <= maxMembers1 and 1 <= k2 <= maxMembers2. etcd's request-id generators carry them as their
// prefix, and the trusted model of idutil's Generator.Next assumes no two generators of the process
// issue one id. A member's id depends only on its peer URL and its cluster's token, so the ids at
// (k1, k2) are the first k1 of the store's maxMembers1 and the first k2 of the compactor's
// maxMembers2: the test checks that each list's ids are those etcd computes at every k (the prefix
// property), then the maxMembers1+maxMembers2 ids together, which covers every pair.
func TestMemberIDs(t *testing.T) {
	all := map[bool][]types.ID{}
	for _, c := range []struct {
		comp  bool
		max   uint64
		token string
	}{{false, maxMembers1, k8setcd3.Token}, {true, maxMembers2, compactor.Token}} {
		names, peers := members(c.max, c.comp)
		// each member's id, computed alone, in the members' order
		var full []types.ID
		for i := range names {
			one := ids(t, names[i:i+1], peers[i:i+1], c.token)
			full = append(full, one[0])
		}
		// the prefix property: the ids etcd computes for the first k members are full[:k]
		for k := uint64(1); k <= c.max; k++ {
			got := ids(t, names[:k], peers[:k], c.token)
			want := map[types.ID]bool{}
			for _, id := range full[:k] {
				want[id] = true
			}
			if uint64(len(got)) != k {
				t.Fatalf("k=%d: %d ids", k, len(got))
			}
			for _, id := range got {
				if !want[id] {
					t.Fatalf("k=%d: id %x not a member's own", k, uint64(id))
				}
			}
		}
		all[c.comp] = full
	}
	seen := map[uint64]bool{}
	for _, id := range append(all[false], all[true]...) {
		low := uint64(id) & 0xffff
		if low == 0 || seen[low] {
			t.Fatalf("member %x: low 16 bits %#x zero or repeated", uint64(id), low)
		}
		seen[low] = true
	}
}

// TestAddrs checks that the two clusters' addresses (the members' peer and client addresses and
// the bridges') and data directories are disjoint for every 1 <= k1 <= maxMembers1 and
// 1 <= k2 <= maxMembers2: each cluster's lists at k are the first k of its lists at its maximum, so
// checking the maxima covers every pair.
func TestAddrs(t *testing.T) {
	seen := map[string]bool{}
	dirs := map[string]bool{}
	add := func(a string) {
		if seen[a] {
			t.Fatalf("address %s twice", a)
		}
		seen[a] = true
	}
	for _, c := range []struct {
		pfx                  string
		max, peer, cli, brdg uint64
	}{{"k8setcd3N", maxMembers1, k8setcd3.PeerBase, k8setcd3.ClientBase, k8setcd3.BridgeBase},
		{"k8scompactorN", maxMembers2, compactor.PeerBase, compactor.ClientBase, compactor.BridgeBase}} {
		for i, m := range etcdstart.Members(c.pfx, c.max, c.peer, c.cli) {
			add(m.Peer)
			add(m.Client)
			add("127.0.0.1:" + strconv.FormatUint(c.brdg+uint64(i), 10))
			d := walarea.DataDir(m.Name)
			if dirs[d] {
				t.Fatalf("data directory %s twice", d)
			}
			dirs[d] = true
		}
	}
}

// TestMain runs Main at three members for the store with one schedule per cluster, the store's
// member 0 isolated and mended, the compactor's member 1 isolated and mended with member 2's
// bridge blackholed meanwhile: neither driver panics, and Main returns.
func TestMain(t *testing.T) {
	t.Chdir(t.TempDir())
	walarea.ResetFamily(t, "k8setcd3N", "k8scompactorN")
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
	Main(3, 4, 60, 0, 0, sched1, 3, sched2)
	t.Logf("Main took %v", time.Since(start))

	// both workloads ran: the store's revision moved past its seeds, and the compactors wrote
	// compact_rev_key
	for _, c := range []struct{ ep, key string }{
		{"127.0.0.1:21000", "/registry/objs/"}, {"127.0.0.1:24000", "compact_rev_key"}} {
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
