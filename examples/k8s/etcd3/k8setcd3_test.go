package etcd3

import (
	"fmt"
	"os"
	"os/exec"
	"strconv"
	"strings"
	"testing"
	"time"

	"github.com/anishathalye/porcupine"
	"github.com/mit-pdos/etcd-grove/examples/lib/cluster3"
	"github.com/mit-pdos/etcd-grove/examples/lib/etcdstart"
	"github.com/mit-pdos/etcd-grove/examples/lib/walarea"
	"go.etcd.io/etcd/client/pkg/v3/types"
	"go.etcd.io/etcd/server/v3/etcdserver/api/membership"
	"go.uber.org/zap"
)

// TestMainLinearizable runs the driver, in a process of its own (inChild: Main leaves its member
// running, whose files must not be removed under it): the store's history is linearizable under
// Model (Main panics otherwise), and the run reaches the check.
func TestMainLinearizable(t *testing.T) {
	inChild(t, "TestMainLinearizable", "", func(t *testing.T) {
		r := Main(4, 60, 0, 0)
		if r != porcupine.Ok {
			t.Fatalf("Main: %v, want Ok", r)
		}
	})
}

// The model's answers on the seeded store: a no-op update of a non-canonical item rewrites it
// (D30g), a no-op update of a canonical one does not.
func TestModelNoopRewrite(t *testing.T) {
	st := mstore{rv: 1}
	st = mstore{items: setItem(st.items, item{key: "ns-1/a", obj: Obj{Namespace: "ns-1", Name: "a", Value: "x", ResourceVersion: 2}, canon: false}), rv: 2}
	st1, o1 := mstep(Input{Kind: KUpdate, Key: "ns-1/a", NoOp: true}, st)
	if st1.rv != 3 || o1.RV != 3 || o1.Value != "x" {
		t.Fatalf("no-op on non-canonical: %+v %+v", st1, o1)
	}
	st2, o2 := mstep(Input{Kind: KUpdate, Key: "ns-1/a", NoOp: true}, st1)
	if st2.rv != 3 || o2.RV != 3 {
		t.Fatalf("no-op on canonical: %+v %+v", st2, o2)
	}
	_, o3 := mstep(Input{Kind: KDelete, Key: "ns-1/a", HasReject: true, Reject: ""}, st2)
	if o3.Err != ERejected {
		t.Fatalf("rejected delete: %+v", o3)
	}
	_, o4 := mstep(Input{Kind: KGet, Key: "ns-1/c"}, st2)
	if o4.Err != ENotFound || o4.ErrKey != "/registry/objs/ns-1/c" || o4.ErrRV != 3 {
		t.Fatalf("missing get: %+v", o4)
	}
}

// testK is the member count of the cluster tests: K8SETCD3_K, 3 by default.
func testK(t *testing.T) uint64 {
	v := os.Getenv("K8SETCD3_K")
	if v == "" {
		return 3
	}
	k, err := strconv.ParseUint(v, 10, 64)
	if err != nil || k == 0 || k > maxMembers {
		t.Fatalf("K8SETCD3_K=%q: want 1 to %d", v, maxMembers)
	}
	return k
}

// TestMainCluster runs MainCluster once, at testK members, in a process of its own (inChild): the
// store's history over the cluster is linearizable under Model (MainCluster panics otherwise), and
// the run reaches the check.
func TestMainCluster(t *testing.T) {
	k := testK(t)
	inChild(t, "TestMainCluster", "", func(t *testing.T) {
		r := MainCluster(k, 4, 60, 0, 0)
		if r != porcupine.Ok {
			t.Fatalf("MainCluster(%d): %v, want Ok", k, r)
		}
	})
}

// inChild runs body, which starts a cluster on fixed ports and leaves it running,
// in a process of its own: the test binary re-executed on the test test (and its subtest sub, if
// not empty), in a fresh data directory, with K8SETCD3_CHILD set. The parent removes the directory
// once the child has exited, so no member runs while its files are removed (a member whose files
// are removed under it panics at its next snapshot, "failed to release wal": the premise
// storage.diskOk's releaseOk excludes that). Two clusters in one process would collide on the
// ports, so every cluster test runs this way.
func inChild(t *testing.T, test string, sub string, body func(t *testing.T)) {
	if os.Getenv("K8SETCD3_CHILD") != "" {
		t.Chdir(os.Getenv("K8SETCD3_DIR"))
		// the members' WAL areas (wal-link P2): every member a child starts
		walarea.Reset(t, "k8setcd3")
		walarea.ResetFamily(t, "k8setcd3N")
		body(t)
		return
	}
	dir, err := os.MkdirTemp("", "k8setcd3c-")
	if err != nil {
		t.Fatal(err)
	}
	defer os.RemoveAll(dir)
	run := "^" + test + "$"
	if sub != "" {
		run += "/^" + sub + "$"
	}
	cmd := exec.Command(os.Args[0], "-test.run", run, "-test.v", "-test.count=1")
	cmd.Env = append(os.Environ(), "K8SETCD3_CHILD=1", "K8SETCD3_DIR="+dir, "K8SETCD3_SCHED="+sub)
	out, err := cmd.CombinedOutput()
	for _, l := range strings.Split(string(out), "\n") {
		if strings.Contains(l, ".go:") || strings.Contains(l, "panic") || strings.Contains(l, "FAIL") {
			t.Log(strings.TrimSpace(l))
		}
	}
	if err != nil {
		t.Fatalf("%s: the child failed: %v", run, err)
	}
	// a child that ran no test (a mistyped name) also exits 0
	name := test
	if sub != "" {
		name += "/" + sub
	}
	if !strings.Contains(string(out), "--- PASS: "+name+" ") {
		t.Fatalf("%s: the child did not report --- PASS: %s", run, name)
	}
}

// maxMembers is the bound of the cluster theorems' member count.
const maxMembers = 1000

// idsOf returns the member ids etcd computes for startCluster(k)'s cluster at the token token (from
// the peer URLs, as bootstrap does), without starting it.
func idsOf(t *testing.T, k uint64, token string) []types.ID {
	ms := etcdstart.Members("k8setcd3N", k, PeerBase, ClientBase)
	urls := types.URLsMap{}
	for _, m := range ms {
		u, err := types.NewURLs([]string{"http://" + m.Peer})
		if err != nil {
			t.Fatal(err)
		}
		urls[m.Name] = u
	}
	cl, err := membership.NewClusterFromURLsMap(zap.NewNop(), token, urls)
	if err != nil {
		t.Fatal(err)
	}
	return cl.MemberIDs()
}

// idsOk says whether the ids' 16 low bits are distinct and not 0.
func idsOk(ids []types.ID) bool {
	seen := map[uint64]bool{}
	for _, id := range ids {
		low := uint64(id) & 0xffff
		if low == 0 || seen[low] {
			return false
		}
		seen[low] = true
	}
	return true
}

// TestMemberIDs checks the cluster theorems' premise on the member ids (their 16 low bits distinct
// and not 0: etcd's request ids carry them as the member's prefix) for every member count
// 1 <= k <= maxMembers, from the ids etcd computes for startCluster(k)'s cluster. It starts no
// cluster. (The ids of the first k members do not depend on k, so k = maxMembers decides it.)
func TestMemberIDs(t *testing.T) {
	for k := uint64(1); k <= maxMembers; k++ {
		ids := idsOf(t, k, Token)
		if uint64(len(ids)) != k || !idsOk(ids) {
			t.Fatalf("k=%d: the ids' low 16 bits are zero or repeated", k)
		}
	}
}

// TestFindToken (only with K8SETCD3_FIND_TOKEN set) prints the first "k8setcd3N-<i>" at which
// TestMemberIDs passes: how Token was chosen.
func TestFindToken(t *testing.T) {
	if os.Getenv("K8SETCD3_FIND_TOKEN") == "" {
		t.Skip("set K8SETCD3_FIND_TOKEN to run")
	}
	for i := 0; i < 100000; i++ {
		tok := "k8setcd3N-" + strconv.Itoa(i)
		if idsOk(idsOf(t, maxMembers, tok)) {
			t.Logf("token %s", tok)
			return
		}
	}
	t.Fatal("none found")
}

// TestAddrs checks the members' and bridges' addresses at k = 3.
func TestAddrs(t *testing.T) {
	ms := etcdstart.Members("k8setcd3N", 3, PeerBase, ClientBase)
	for i, m := range ms {
		want := etcdstart.Member{
			Name:   fmt.Sprintf("k8setcd3N-%d", i),
			Peer:   fmt.Sprintf("127.0.0.1:%d", 20000+i),
			Client: fmt.Sprintf("127.0.0.1:%d", 21000+i),
		}
		if m != want {
			t.Fatalf("member %d: got %v, want %v", i, m, want)
		}
		if b := bridgeAddr(uint64(i)); b != fmt.Sprintf("127.0.0.1:%d", 22000+i) {
			t.Fatalf("bridge %d: got %s", i, b)
		}
	}
}

// cutSteps returns the steps that, after delay, cut (or mend, if !cut) member m's links to the k-1
// others.
func cutSteps(delay time.Duration, k int, m int, cut bool) []cluster3.Step {
	kind := cluster3.PeerCut
	if !cut {
		kind = cluster3.PeerMend
	}
	var steps []cluster3.Step
	for o := 0; o < k; o++ {
		if o != m {
			steps = append(steps, cluster3.Step{Delay: delay, Kind: kind, A: m, B: o})
			delay = 0
		}
	}
	return steps
}

// partitionSchedules are the partition tests' schedules for k members, by name. (At k = 1 the peer
// steps are empty: a member has no link to cut; the client steps remain.)
func partitionSchedules(k int) map[string][]cluster3.Step {
	ms := time.Millisecond
	// each member isolated in turn from the others (both directions), then mended: the leader is
	// isolated in one of the rounds
	var isolate []cluster3.Step
	// each member in turn cut off from the others for 3s, longer than the election timeout (1-2s:
	// TickMs 100, ElectionTicks 10), then mended: the round of the leader forces a new election
	var election []cluster3.Step
	for m := 0; m < k; m++ {
		isolate = append(isolate, cutSteps(150*ms, k, m, true)...)
		isolate = append(isolate, cutSteps(300*ms, k, m, false)...)
		election = append(election, cutSteps(100*ms, k, m, true)...)
		election = append(election, cutSteps(3*time.Second, k, m, false)...)
	}
	// the clients' connections to each member closed, twice
	var drop []cluster3.Step
	for r := 0; r < 2; r++ {
		for m := 0; m < k; m++ {
			drop = append(drop, cluster3.Step{Delay: 100 * ms, Kind: cluster3.ClientDrop, A: m})
		}
	}
	// one round modeled on the k8s compactor's TestMainPartition: member 0 isolated with the last
	// member's bridge blackholed, then mended, the last member unblackholed and member (1 mod k)'s
	// connections dropped
	mixed := cutSteps(100*ms, k, 0, true)
	mixed = append(mixed, cluster3.Step{Kind: cluster3.ClientBlackhole, A: k - 1})
	mixed = append(mixed, cutSteps(300*ms, k, 0, false)...)
	mixed = append(mixed, cluster3.Step{Kind: cluster3.ClientUnblackhole, A: k - 1},
		cluster3.Step{Kind: cluster3.ClientDrop, A: 1 % k})
	return map[string][]cluster3.Step{
		"isolate":  isolate,
		"election": election,
		// member 0's clients cut off it (every byte dropped) for 10s, then back: keepalive closes
		// the dead transport, the client fails over, and the unblackhole runs before the check ends
		"blackhole": {
			{Delay: 100 * ms, Kind: cluster3.ClientBlackhole, A: 0},
			{Delay: 10 * time.Second, Kind: cluster3.ClientUnblackhole, A: 0},
		},
		"drop":  drop,
		"mixed": mixed,
	}
}

// TestMainPartition runs MainPartition at testK members once per schedule (K8SETCD3_SCHED names
// one; all by default), each in a process of its own (inChild): the store's history over the partitioned
// cluster is linearizable under Model (MainPartition panics otherwise), and the run reaches the
// check.
func TestMainPartition(t *testing.T) {
	only := os.Getenv("K8SETCD3_SCHED")
	k := testK(t)
	for name, sched := range partitionSchedules(int(k)) {
		if only != "" && name != only {
			continue
		}
		t.Run(name, func(t *testing.T) {
			inChild(t, "TestMainPartition", name, func(t *testing.T) {
				start := time.Now()
				r := MainPartition(k, 4, 60, 0, 0, sched)
				t.Logf("%s: %v in %v", name, r, time.Since(start))
				if r != porcupine.Ok {
					t.Fatalf("MainPartition(%s): %v, want Ok", name, r)
				}
			})
		})
	}
}

// TestSplitKey checks splitKey's loop against strings.Cut, which it replaces (7e-3b: Perennial has
// no model of Cut).
func TestSplitKey(t *testing.T) {
	for _, k := range []string{"", "/", "a", "a/", "/b", "ns-1/pod-1", "ns-11/pod-1/x", "ns//p"} {
		ns, name := splitKey(k)
		cns, cname, _ := strings.Cut(k, "/")
		if ns != cns || name != cname {
			t.Fatalf("splitKey(%q) = %q, %q; strings.Cut: %q, %q", k, ns, name, cns, cname)
		}
	}
}
