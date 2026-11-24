package dist

import (
	"fmt"
	"math/rand/v2"
	"os"
	"strconv"
	"strings"
	"testing"
	"time"

	"github.com/mit-pdos/etcd-grove/examples/etcd/auth"
	"github.com/mit-pdos/etcd-grove/examples/etcd/dist/deployment"
	"github.com/mit-pdos/etcd-grove/examples/lib/robust"
)

// TestMain runs a member, an orchestrator or a client machine instead of the tests when the test
// started this binary as one (DIST_PROC set: its role, the deployment's file and its index are the
// arguments, RunProcess).
func TestMain(m *testing.M) {
	if os.Getenv("DIST_PROC") != "" {
		if err := RunProcess(os.Args[1:]); err != nil {
			fmt.Fprintln(os.Stderr, err)
			os.Exit(2)
		}
		os.Exit(0)
	}
	// The machines inherit this process's environment: give them the one the theorems' premises
	// describe (verifyEnvOff: ETCD_VERIFY off; no proxy variable set, so that no non-loopback
	// dial or request goes through a proxy: examples/premisefix/proxyenv).
	for _, k := range []string{"ETCD_VERIFY", "HTTP_PROXY", "http_proxy", "HTTPS_PROXY", "https_proxy", "NO_PROXY", "no_proxy"} {
		os.Unsetenv(k)
	}
	os.Exit(m.Run())
}

// testNodes are client machine addresses for the workloads ws, apart from the members' (10.78.j.c+1).
func testNodes(ws []Workload) [][]string {
	nodes := [][]string{}
	for j, w := range ws {
		as := []string{}
		for c := 0; c < deployment.NodeCount(w); c++ {
			as = append(as, fmt.Sprintf("10.78.%d.%d:%d", j, c+1, NodePort))
		}
		nodes = append(nodes, as)
	}
	return nodes
}

// TestWellFormed checks the deployment predicate's Go mirror on random deployments (every machine's
// program's first check passes on them: the deployments TestDist runs are of this kind) and on
// ill-formed ones.
func TestWellFormed(t *testing.T) {
	addr := func(i int) (string, string) {
		return fmt.Sprintf("10.77.%d.1:2380", i+1), fmt.Sprintf("10.77.%d.1:2379", i+1)
	}
	random := func() Deployment {
		ws := RandomWorkloads(ShortSizes)
		d, err := RandomDeployment("wf", 3, addr, ws, testNodes(ws))
		if err != nil {
			t.Fatalf("a random deployment is not well formed: %v: %v", d, err)
		}
		return d
	}
	kinds := map[deployment.Kind]bool{}
	for n := 0; n < 500; n++ {
		d := random()
		for _, w := range d.Workloads {
			kinds[w.Kind] = true
		}
	}
	if len(kinds) != 11 {
		t.Errorf("random deployments covered %d kinds of workload, not 11", len(kinds))
	}
	d := random()
	bad := d
	bad.Members = append([]Member(nil), d.Members...)
	bad.Members[1].Client = bad.Members[0].Client
	if WellFormed(bad) == nil {
		t.Error("a repeated address passed")
	}
	bad.Members[1].Client = "10.77.2.1:40000"
	if WellFormed(bad) == nil {
		t.Error("an ephemeral port passed")
	}
	if deployment.AddrOk("010.1.1.1:80") || deployment.AddrOk("10.1.1:80") || !deployment.AddrOk("10.77.1.1:2379") {
		t.Error("AddrOk")
	}
	// the client machines: their number, their addresses
	kv := []Workload{{Kind: deployment.KV, Clients: 2, Ops: 3}}
	d, err := RandomDeployment("wf", 3, addr, kv, testNodes(kv))
	if err != nil {
		t.Fatal(err)
	}
	bad = d
	bad.Nodes = [][]string{{d.Nodes[0][0]}}
	if WellFormed(bad) == nil {
		t.Error("a missing client machine passed")
	}
	bad.Nodes = [][]string{{d.Nodes[0][0], d.Members[0].Peer}}
	if WellFormed(bad) == nil {
		t.Error("a client machine at a member's address passed")
	}
	bad.Nodes = [][]string{{d.Nodes[0][0], "10.78.0.1"}}
	if WellFormed(bad) == nil {
		t.Error("a client machine address without a port passed")
	}
	bad.Nodes = nil
	if WellFormed(bad) == nil {
		t.Error("no client machine list passed")
	}
	// the workloads' bounds and kinds
	bad = d
	bad.Workloads = []Workload{{Kind: deployment.KV, Clients: 2, Ops: 1 << 59}}
	if WellFormed(bad) == nil {
		t.Error("kv's clients*ops >= 2^60 passed")
	}
	bad.Workloads = []Workload{{Kind: deployment.Durable + 1}}
	bad.Nodes = [][]string{{}}
	if WellFormed(bad) == nil {
		t.Error("an unknown kind passed")
	}
}

// TestNodeCount checks that the auth workload's client machines are its principals.
func TestNodeCount(t *testing.T) {
	if deployment.NodeCount(Workload{Kind: deployment.Auth}) != len(auth.Principals()) {
		t.Error("deployment.AuthPrincipals is not len(auth.Principals())")
	}
}

// TestNode checks Deployment.Node against Lean's nodeList: the client machines in the workloads'
// order, then by index.
func TestNode(t *testing.T) {
	d := Deployment{Workloads: []Workload{{Kind: deployment.KV, Clients: 2}, {Kind: deployment.Compact},
		{Kind: deployment.Watch, Clients: 1}}, Nodes: [][]string{{"a", "b"}, {}, {"c"}}}
	want := []string{"a", "b", "c"}
	for n := -1; n <= len(want); n++ {
		j, c, ok := d.Node(n)
		if ok != (0 <= n && n < len(want)) || ok && d.Nodes[j][c] != want[n] {
			t.Errorf("Node(%d) = %d, %d, %v", n, j, c, ok)
		}
	}
}

// wanted says whether the workloads ws have one of a kind DIST_WANT names (comma-separated kind
// names, e.g. auth,authLease), or DIST_WANT is unset: to aim the random deployments at some
// workloads.
func wanted(ws []Workload) bool {
	want := os.Getenv("DIST_WANT")
	if want == "" {
		return true
	}
	for _, w := range ws {
		for _, k := range strings.Split(want, ",") {
			if w.Kind.String() == k {
				return true
			}
		}
	}
	return false
}

// deployRound runs one random deployment of k members: its network, its cluster, its clients
// under the faults; it fails t on a failure.
func deployRound(t *testing.T, round int, netns bool, crash string, sz Sizes, deadline time.Duration) {
	exe, err := os.Executable()
	if err != nil {
		t.Fatal(err)
	}
	n, err := robust.NewNetworkOrLocal(netns, "ed")
	if err != nil {
		t.Fatal(err)
	}
	defer n.Close()
	ms, addr, err := MemberMachines(n, 3, 20000+2*rand.IntN(5000))
	if err != nil {
		t.Fatal(err)
	}
	if s := os.Getenv("DIST_OPS"); s != "" {
		if n, err := strconv.Atoi(s); err == nil && n > 0 {
			sz.KVOps, sz.WriterOps = n, n
		}
	}
	ws := RandomWorkloads(sz)
	for tries := 0; !wanted(ws) && tries < 1000; tries++ {
		ws = RandomWorkloads(sz)
	}
	nms, nodes, err := NodeMachines(n, ws)
	if err != nil {
		t.Fatal(err)
	}
	tag := fmt.Sprintf("d%d-%d", os.Getpid(), round)
	d, err := RandomDeployment(tag, 3, addr, ws, nodes)
	if err != nil {
		t.Fatalf("%v: %v", d, err)
	}
	cfg := robust.Config{Crash: crash, CrashPause: 2 * time.Second, Downtime: time.Second, Netns: netns,
		NetPause: time.Second, NetHold: 2 * time.Second, Deadline: deadline,
		FaultsAtStart: os.Getenv("DIST_FAULTS") == "start", SetupWait: 3 * time.Minute}
	work, err := os.MkdirTemp("", "etcddist-")
	if err != nil {
		t.Fatal(err)
	}
	start := time.Now()
	r, err := robust.NewRun(cfg, robust.Command{Path: exe, Env: []string{"DIST_PROC=1"}}, n, work)
	if err != nil {
		t.Fatal(err)
	}
	c, err := Start(d, r, n, ms, nms)
	if err != nil {
		r.Stop()
		os.RemoveAll(work)
		t.Fatalf("%v: %v", d, err)
	}
	res := c.Run()
	r.Stop()
	c.Stop()
	t.Logf("round %d: %v (%v)\n  %s; network: %s\n  %s", round, d, time.Since(start).Round(time.Second),
		&r.Stats, r.NetStats(), strings.Join(res.Lines, "\n  "))
	if res.Err != nil {
		t.Errorf("round %d: %v (work directory kept: %s)", round, res.Err, work)
		return
	}
	os.RemoveAll(work)
}

// TestDist runs random deployments of three members, each with a mix of compatible workloads on
// client machines of their own, while members crash (kills, and power losses where the device
// mapper is available) and, on network namespaces, the network fails. It runs only with DIST_RUN
// set (minutes per deployment); -short runs one small deployment, otherwise DIST_ROUNDS (default
// 4) larger ones. The faults start once every workload's set-up is done (client.MainReady), or,
// with DIST_FAULTS=start, from the start; DIST_WANT=kind,... keeps only random deployments with a
// workload of those kinds; DIST_OPS=n sets the kv clients' and the writers' operations to n each.
// Network namespaces need root with CAP_NET_ADMIN: without them, the test runs again where it
// can make them (robust.RerunTest: a container's root in a user namespace of its own, a non-root by
// sudo -n), and in the local mode (one loopback address, no network faults) if it cannot.
func TestDist(t *testing.T) {
	if os.Getenv("DIST_RUN") == "" {
		t.Skip("set DIST_RUN=1 to run (minutes per deployment; namespaces need root)")
	}
	if robust.RerunTest(t, "TestDist", "2h", testing.Short(), []string{"DIST_RUN=1", "DIST_ROUNDS=" + os.Getenv("DIST_ROUNDS"),
		"DIST_FAULTS=" + os.Getenv("DIST_FAULTS"), "DIST_WANT=" + os.Getenv("DIST_WANT"), "DIST_OPS=" + os.Getenv("DIST_OPS")}) {
		return
	}
	netns := robust.NetnsAvailable() == nil
	crash := robust.CrashKill
	if robust.PowerAvailable() == nil {
		crash = robust.CrashMixed
	}
	if testing.Short() {
		deployRound(t, 1, netns, crash, ShortSizes, 5*time.Minute)
		return
	}
	rounds := 4
	if s := os.Getenv("DIST_ROUNDS"); s != "" {
		if r, err := strconv.Atoi(s); err == nil && r > 0 {
			rounds = r
		}
	}
	for r := 1; r <= rounds && !t.Failed(); r++ {
		deployRound(t, r, netns, crash, FullSizes, 10*time.Minute)
	}
}
