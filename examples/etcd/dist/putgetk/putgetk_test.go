package putgetk

import (
	"fmt"
	"math/rand/v2"
	"os"
	"path/filepath"
	"strconv"
	"strings"
	"testing"
	"time"

	"go.etcd.io/etcd/client/pkg/v3/types"
	"go.etcd.io/etcd/server/v3/etcdserver/api/membership"
	"go.uber.org/zap"

	"github.com/mit-pdos/etcd-grove/examples/lib/etcdstart"
	"github.com/mit-pdos/etcd-grove/examples/lib/robust"
)

// K is the member count of the test's deployments (and of putgetK_safe's first statement).
const K = 3

// TestMain runs a member or the client instead of the tests when the test started this binary as
// one (PUTGETK_PROC set; the arguments: "member" I PEERS CLIENTS, the lists comma-separated, or
// "client" CLIENT): what cmd/member and cmd/client do, for a binary that is both (the test binary).
func TestMain(m *testing.M) {
	if os.Getenv("PUTGETK_PROC") != "" {
		a := os.Args[1:]
		switch {
		case len(a) == 4 && a[0] == "member":
			i, err := strconv.ParseUint(a[1], 10, 64)
			if err != nil {
				os.Exit(2)
			}
			Member(i, strings.Split(a[2], ","), strings.Split(a[3], ","))
			fmt.Fprintln(os.Stderr, "member: a step failed")
			os.Exit(1)
		case len(a) == 2 && a[0] == "client":
			if Client(a[1]) {
				fmt.Println("putgetk: checked")
			} else {
				fmt.Println("putgetk: ended")
			}
			os.Exit(0)
		}
		fmt.Fprintln(os.Stderr, "usage: member I PEERS CLIENTS | client CLIENT")
		os.Exit(2)
	}
	// The machines inherit this process's environment: give them the one the theorems' premises
	// describe (verifyEnvOff: ETCD_VERIFY off; no proxy variable set: examples/premisefix/proxyenv).
	for _, k := range []string{"ETCD_VERIFY", "HTTP_PROXY", "http_proxy", "HTTPS_PROXY", "https_proxy", "NO_PROXY", "no_proxy"} {
		os.Unsetenv(k)
	}
	os.Exit(m.Run())
}

// theoremAddrs are putgetK_safe's addresses (k = 3): member i's machine 10.77.(i+1).1, its peer
// address on port 2380, its client address on port 2379 (the namespace mode's, below: the members'
// machines are the network's first three).
func theoremAddrs() (peers, clients []string) {
	for i := 1; i <= K; i++ {
		peers = append(peers, fmt.Sprintf("10.77.%d.1:2380", i))
		clients = append(clients, fmt.Sprintf("10.77.%d.1:2379", i))
	}
	return
}

// TestMemberIDs checks putgetK_safe's premise on the member ids (BootCore: their 16 low bits
// distinct and not 0) at the theorem's addresses, from the ids etcd computes for the cluster (its
// peer URLs and Token, as bootstrap does). It starts no cluster.
func TestMemberIDs(t *testing.T) {
	peers, _ := theoremAddrs()
	urls := types.URLsMap{}
	for j, p := range peers {
		u, err := types.NewURLs([]string{"http://" + p})
		if err != nil {
			t.Fatal(err)
		}
		urls[Name(uint64(j))] = u
	}
	cl, err := membership.NewClusterFromURLsMap(zap.NewNop(), Token, urls)
	if err != nil {
		t.Fatal(err)
	}
	seen := map[uint64]bool{}
	for _, id := range cl.MemberIDs() {
		low := uint64(id) & 0xffff
		if low == 0 || seen[low] {
			t.Fatalf("member %x: low 16 bits %#x zero or repeated", uint64(id), low)
		}
		seen[low] = true
	}
	if len(seen) != K {
		t.Fatalf("%d ids", len(seen))
	}
}

// TestName checks the members' names.
func TestName(t *testing.T) {
	if Name(0) != "putgetk-0" || Name(12) != "putgetk-12" {
		t.Fatal(Name(0), Name(12))
	}
}

// round runs one deployment: K member machines and the client's on a network of their own
// (namespaces if netns, else the one loopback address), the members started, then, once every
// member's client address accepts a connection from the client's machine, the client. With faults,
// the network fails from the client's start on (partitions and link faults over every machine; no
// crash: the theorem's machines never crash). It returns the client's result line; a panic, a
// member exiting on its own or a client not done by the deadline fails t.
func round(t *testing.T, i int, netns bool, faults bool) string {
	exe, err := os.Executable()
	if err != nil {
		t.Fatal(err)
	}
	n, err := robust.NewNetworkOrLocal(netns, "pk")
	if err != nil {
		t.Fatal(err)
	}
	defer n.Close()
	var mms []*robust.Machine
	for j := 0; j < K; j++ {
		m, err := n.AddMachine(fmt.Sprintf("member-%d", j))
		if err != nil {
			t.Fatal(err)
		}
		mms = append(mms, m)
	}
	cm, err := n.AddMachine("client")
	if err != nil {
		t.Fatal(err)
	}
	var peers, clients []string
	if n.Namespaces() {
		peers, clients = theoremAddrs()
		for j, m := range mms {
			if !strings.HasPrefix(peers[j], m.IP+":") {
				t.Fatalf("member %d's machine is %s, not the theorem's %s", j, m.IP, peers[j])
			}
		}
	} else {
		base := 21000 + 2*K*rand.IntN(2000)
		for j, m := range mms {
			peers = append(peers, m.IP+":"+strconv.Itoa(base+2*j))
			clients = append(clients, m.IP+":"+strconv.Itoa(base+2*j+1))
		}
	}
	cfg := robust.Config{Crash: robust.CrashKill, Netns: netns, Deadline: 2 * time.Minute,
		FaultsAtStart: true, SetupWait: time.Minute}
	if faults {
		cfg.NetPause, cfg.NetHold = 300*time.Millisecond, time.Second
	}
	work, err := os.MkdirTemp("", "putgetkdist-")
	if err != nil {
		t.Fatal(err)
	}
	r, err := robust.NewRun(cfg, robust.Command{Path: exe, Env: []string{"PUTGETK_PROC=1"}}, n, work)
	if err != nil {
		t.Fatal(err)
	}
	defer r.Stop()
	// each member's data directory and WAL area: empty directories of its own, at the paths
	// etcdstart.StartMember uses (the theorem's MemberFiles)
	g := r.NewGroup()
	for j, m := range mms {
		mb, err := g.Add(Name(uint64(j)), m)
		if err != nil {
			t.Fatal(err)
		}
		name := Name(uint64(j)) + ".etcd"
		links := []string{filepath.Join(etcdstart.DataBase, name), filepath.Join(etcdstart.WALBase, name)}
		for l, sub := range []string{"data", "wal"} {
			if err := os.MkdirAll(filepath.Join(mb.Dir, sub), 0o755); err != nil {
				t.Fatal(err)
			}
			if err := robust.Symlink(filepath.Join(mb.Dir, sub), links[l]); err != nil {
				t.Fatal(err)
			}
			defer os.Remove(links[l])
		}
		mb.Args = []string{"member", strconv.Itoa(j), strings.Join(peers, ","), strings.Join(clients, ",")}
	}
	if err := g.Start(); err != nil {
		t.Fatal(err)
	}
	// a liveness wait only (the test's, not the programs'): every member's listener is up
	for j, c := range clients {
		up := false
		for k := 0; k < 300 && r.Err() == nil; k++ {
			if conn, err := cm.Dial(c, time.Second); err == nil {
				conn.Close()
				up = true
				break
			}
			time.Sleep(100 * time.Millisecond)
		}
		if !up {
			t.Fatalf("round %d: member %d's client address %s never accepted (%v); its log:\n%s", i, j, c,
				r.Err(), robust.Tail(r.LogPath(Name(uint64(j))), 40))
		}
	}
	machines := append(append([]*robust.Machine(nil), mms...), cm)
	lines := r.RunClients(nil, []robust.Client{{Name: "client", Machine: cm, Args: []string{"client", clients[0]},
		Ready: filepath.Join(work, "client.ready")}}, machines)
	t.Logf("round %d (faults %v): %s; network: %s", i, faults, lines[0], r.NetStats())
	if err := r.Err(); err != nil {
		t.Fatalf("round %d: %v (work directory kept: %s)", i, err, work)
	}
	os.RemoveAll(work)
	return lines[0]
}

// TestPutGetK runs putgetK_safe's deployment (notes/putget-dist-plan.md §13): K member machines and
// one client machine, no crash. The first round has no fault and must check; the others
// (PUTGETK_ROUNDS, default 4; -short: 1) have network faults on namespaces from the client's start
// (partitions, one-way partitions, link faults over every machine), where the check runs or a step
// fails, and nothing panics. It runs only with DIST_RUN set (it makes processes, and network
// namespaces where it can: robust.RerunTest, as putget's TestPutGet).
func TestPutGetK(t *testing.T) {
	if os.Getenv("DIST_RUN") == "" {
		t.Skip("set DIST_RUN=1 to run (processes; namespaces need root)")
	}
	if robust.RerunTest(t, "TestPutGetK", "30m", testing.Short(), []string{"DIST_RUN=1",
		"PUTGETK_ROUNDS=" + os.Getenv("PUTGETK_ROUNDS")}) {
		return
	}
	netns := robust.NetnsAvailable() == nil
	if l := round(t, 0, netns, false); !strings.HasSuffix(l, "checked") {
		t.Fatalf("the fault-free round did not check: %q", l)
	}
	rounds := 4
	if s := os.Getenv("PUTGETK_ROUNDS"); s != "" {
		if v, err := strconv.Atoi(s); err == nil && v >= 0 {
			rounds = v
		}
	}
	if testing.Short() {
		rounds = 1
	}
	if !netns {
		t.Log("no network namespaces: the faulty rounds are skipped (local mode)")
		return
	}
	checked := 0
	for i := 1; i <= rounds; i++ {
		if strings.HasSuffix(round(t, i, netns, true), "checked") {
			checked++
		}
	}
	t.Logf("faulty rounds: %d of %d checked", checked, rounds)
}
