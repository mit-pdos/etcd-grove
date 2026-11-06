package etcd3

import (
	"os"
	"testing"
	"time"

	"github.com/anishathalye/porcupine"
	"github.com/mit-pdos/etcd-grove/examples/lib/cluster3"
	"go.etcd.io/etcd/client/pkg/v3/types"
	"go.etcd.io/etcd/server/v3/etcdserver/api/membership"
	"go.uber.org/zap"
)

// TestMain runs the driver: the store's history is linearizable under Model (Main panics
// otherwise), and the run reaches the check.
func TestMainLinearizable(t *testing.T) {
	os.RemoveAll("k8setcd3.etcd")
	defer os.RemoveAll("k8setcd3.etcd")
	r := Main(4, 60)
	if r != porcupine.Ok {
		t.Fatalf("Main: %v, want Ok", r)
	}
}

// The model's answers on the seeded store: a no-op update of a non-canonical item rewrites it
// (D30g), a no-op update of a canonical one does not.
func TestModelNoopRewrite(t *testing.T) {
	st := mstore{rv: 1}
	st = mstore{items: setItem(st.items, item{key: "a", obj: Obj{Name: "a", Value: "x", ResourceVersion: 2}, canon: false}), rv: 2}
	st1, o1 := mstep(Input{Kind: KUpdate, Key: "a", NoOp: true}, st)
	if st1.rv != 3 || o1.RV != 3 || o1.Value != "x" {
		t.Fatalf("no-op on non-canonical: %+v %+v", st1, o1)
	}
	st2, o2 := mstep(Input{Kind: KUpdate, Key: "a", NoOp: true}, st1)
	if st2.rv != 3 || o2.RV != 3 {
		t.Fatalf("no-op on canonical: %+v %+v", st2, o2)
	}
	_, o3 := mstep(Input{Kind: KDelete, Key: "a", Reject: "x"}, st2)
	if o3.Err != ERejected {
		t.Fatalf("rejected delete: %+v", o3)
	}
	_, o4 := mstep(Input{Kind: KGet, Key: "c"}, st2)
	if o4.Err != ENotFound || o4.ErrKey != "/registry/objs/c" || o4.ErrRV != 3 {
		t.Fatalf("missing get: %+v", o4)
	}
}

// TestMainCluster runs MainCluster once, in a fresh data directory: the store's history over the
// three-member cluster is linearizable under Model (MainCluster panics otherwise), and the run
// reaches the check.
func TestMainCluster(t *testing.T) {
	t.Chdir(t.TempDir())
	r := MainCluster(4, 60)
	if r != porcupine.Ok {
		t.Fatalf("MainCluster: %v, want Ok", r)
	}
}

// TestMemberIDs checks clusterConfig's member ids, as etcd computes them from the names, peer URLs
// and token: their low 16 bits are nonzero and distinct (cluster3's premise on the ids).
func TestMemberIDs(t *testing.T) {
	cfg := clusterConfig()
	urls, err := types.NewURLsMap(cfg.Name1 + "=http://" + cfg.Peer1 + "," + cfg.Name2 + "=http://" +
		cfg.Peer2 + "," + cfg.Name3 + "=http://" + cfg.Peer3)
	if err != nil {
		t.Fatal(err)
	}
	cl, err := membership.NewClusterFromURLsMap(zap.NewNop(), cfg.Token, urls)
	if err != nil {
		t.Fatal(err)
	}
	seen := map[uint64]bool{}
	for _, id := range cl.MemberIDs() {
		low := uint64(id) & 0xffff
		t.Logf("member %x (%s): low 16 bits %#x", uint64(id), cl.Member(id).Name, low)
		if low == 0 || seen[low] {
			t.Fatalf("member %x: low 16 bits %#x zero or repeated", uint64(id), low)
		}
		seen[low] = true
	}
}

// partitionSchedules are TestMainPartition's schedules, by name.
func partitionSchedules() map[string][]cluster3.Step {
	ms := time.Millisecond
	// each member isolated in turn from the two others (both directions), then mended: the
	// leader is isolated in one of the three rounds
	var isolate []cluster3.Step
	for m := 0; m < 3; m++ {
		first := true
		for o := 0; o < 3; o++ {
			if o != m {
				d := time.Duration(0)
				if first {
					d = 150 * ms
					first = false
				}
				isolate = append(isolate, cluster3.Step{Delay: d, Kind: cluster3.PeerCut, A: m, B: o})
			}
		}
		first = true
		for o := 0; o < 3; o++ {
			if o != m {
				d := time.Duration(0)
				if first {
					d = 300 * ms
					first = false
				}
				isolate = append(isolate, cluster3.Step{Delay: d, Kind: cluster3.PeerMend, A: m, B: o})
			}
		}
	}
	return map[string][]cluster3.Step{
		"isolate": isolate,
		// member 0's clients cut off it (every byte dropped) for 20s, then back: keepalive closes
		// the dead transport and the client fails over
		"blackhole": {
			{Delay: 100 * ms, Kind: cluster3.ClientBlackhole, A: 0},
			{Delay: 20 * time.Second, Kind: cluster3.ClientUnblackhole, A: 0},
		},
		// the clients' connections to each member closed, repeatedly
		"drop": {
			{Delay: 100 * ms, Kind: cluster3.ClientDrop, A: 0},
			{Delay: 100 * ms, Kind: cluster3.ClientDrop, A: 1},
			{Delay: 100 * ms, Kind: cluster3.ClientDrop, A: 2},
			{Delay: 100 * ms, Kind: cluster3.ClientDrop, A: 0},
			{Delay: 100 * ms, Kind: cluster3.ClientDrop, A: 1},
			{Delay: 100 * ms, Kind: cluster3.ClientDrop, A: 2},
		},
		// as the k8s compactor's TestMainPartition: member 0 isolated with member 2's bridge
		// blackholed, then mended, member 2 unblackholed and member 1's connections dropped
		"mixed": {
			{Delay: 100 * ms, Kind: cluster3.PeerCut, A: 0, B: 1},
			{Kind: cluster3.PeerCut, A: 0, B: 2},
			{Kind: cluster3.ClientBlackhole, A: 2},
			{Delay: 300 * ms, Kind: cluster3.PeerMend, A: 0, B: 1},
			{Kind: cluster3.PeerMend, A: 0, B: 2},
			{Kind: cluster3.ClientUnblackhole, A: 2},
			{Kind: cluster3.ClientDrop, A: 1},
		},
	}
}

// TestMainPartition runs MainPartition once per schedule (K8SETCD3_SCHED names one; all by
// default), each in a fresh data directory: the store's history over the partitioned cluster is
// linearizable under Model (MainPartition panics otherwise), and the run reaches the check.
func TestMainPartition(t *testing.T) {
	only := os.Getenv("K8SETCD3_SCHED")
	for name, sched := range partitionSchedules() {
		if only != "" && name != only {
			continue
		}
		t.Run(name, func(t *testing.T) {
			// a data directory the test does not remove: MainPartition leaves its cluster running,
			// and removing the members' files under them (t.TempDir's cleanup) makes a member's
			// next snapshot panic ("failed to release wal"), after the check
			dir, err := os.MkdirTemp("", "k8setcd3p-")
			if err != nil {
				t.Fatal(err)
			}
			t.Logf("data directory %s", dir)
			t.Chdir(dir)
			start := time.Now()
			r := MainPartition(4, 60, sched)
			t.Logf("%s: %v in %v", name, r, time.Since(start))
			if r != porcupine.Ok {
				t.Fatalf("MainPartition(%s): %v, want Ok", name, r)
			}
		})
	}
}
