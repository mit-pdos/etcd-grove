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

// maxK is the largest member count the tests' random configurations have.
const maxK = 5

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

// randPorts returns 2k distinct ports in 21000-32767 (valid, AddrOK, and below the ephemeral range).
func randPorts(rng *rand.Rand, k int) []int {
	seen := map[int]bool{}
	var ps []int
	for len(ps) < 2*k {
		p := 21000 + rng.IntN(32768-21000)
		if !seen[p] {
			seen[p] = true
			ps = append(ps, p)
		}
	}
	return ps
}

// randConfig returns a random configuration of k members over the hosts ips (member j on
// ips[j % len(ips)]): random distinct valid ports.
func randConfig(rng *rand.Rand, k int, ips []string) (peers, clients []string) {
	ps := randPorts(rng, k)
	for j := 0; j < k; j++ {
		ip := ips[j%len(ips)]
		peers = append(peers, ip+":"+strconv.Itoa(ps[2*j]))
		clients = append(clients, ip+":"+strconv.Itoa(ps[2*j+1]))
	}
	return
}

// randIP returns a random valid IPv4 address (first octet 1-223).
func randIP(rng *rand.Rand) string {
	return fmt.Sprintf("%d.%d.%d.%d", 1+rng.IntN(223), rng.IntN(256), rng.IntN(256), rng.IntN(256))
}

// etcdIDs are the ids etcd computes for the configuration's members (membership's, as bootstrap
// does: the initial cluster's map of each member's one peer URL, and Token), in the members' order.
func etcdIDs(t *testing.T, peers []string) []uint64 {
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
	var ids []uint64
	for j := range peers {
		m := cl.MemberByName(Name(uint64(j)))
		if m == nil {
			t.Fatalf("no member %s", Name(uint64(j)))
		}
		ids = append(ids, uint64(m.ID))
	}
	return ids
}

// TestMemberIDEtcd checks MemberID against the ids etcd computes, over 3000 random configurations
// (1 to 7 members, random addresses): the ids Valid checks are bootstrap's.
func TestMemberIDEtcd(t *testing.T) {
	for seed := uint64(0); seed < 3000; seed++ {
		rng := rand.New(rand.NewPCG(seed, 1))
		k := 1 + rng.IntN(7)
		var ips []string
		for j := 0; j < k; j++ {
			ips = append(ips, randIP(rng))
		}
		peers, _ := randConfig(rng, k, ips)
		for j, id := range etcdIDs(t, peers) {
			if MemberID(peers[j]) != id {
				t.Fatalf("seed %d: member %d (%s): MemberID %x, etcd's %x", seed, j, peers[j], MemberID(peers[j]), id)
			}
		}
	}
}

// TestAddrOK checks AddrOK on the net extension's cases (examples/net/semantics).
func TestAddrOK(t *testing.T) {
	for _, a := range []string{"10.77.1.1:2380", "127.0.0.1:2379", "1.0.0.0:1", "223.255.255.255:65535", "8.8.8.8:61000"} {
		if !AddrOK(a) {
			t.Errorf("AddrOK(%q) = false", a)
		}
	}
	for _, a := range []string{"", "0.1.2.3:80", "224.0.0.1:80", "10.0.0.256:80", "10.0.0.1:0", "10.0.0.1:65536",
		"10.0.0.1:32768", "10.0.0.1:60999", "010.0.0.1:80", "10.0.0.1:080", "10.0.0.1", "10.0.0:80", "10.0.0.1.1:80",
		"localhost:80", ":80", "10.0.0.1:80:1", "10.0.0.1:", "a.b.c.d:80"} {
		if AddrOK(a) {
			t.Errorf("AddrOK(%q) = true", a)
		}
	}
}

// TestValidSeeds is Valid's non-vacuity over many seeds: of 20000 random configurations (1 to 9
// members on random addresses), all but a few (the ids' 16 low bits colliding, by the birthday
// bound about k^2/2^17) pass, and every one Valid refuses has such a collision. Configurations that
// break a rule are refused.
func TestValidSeeds(t *testing.T) {
	pass := 0
	const n = 20000
	for seed := uint64(0); seed < n; seed++ {
		rng := rand.New(rand.NewPCG(seed, 2))
		k := 1 + rng.IntN(9)
		var ips []string
		for j := 0; j < k; j++ {
			ips = append(ips, randIP(rng))
		}
		peers, clients := randConfig(rng, k, ips)
		if Valid(peers, clients) {
			pass++
			continue
		}
		lows := map[uint64]bool{}
		collide := false
		for _, p := range peers {
			low := MemberID(p) & 0xffff
			collide = collide || low == 0 || lows[low]
			lows[low] = true
		}
		if !collide {
			t.Fatalf("seed %d: Valid refused %v %v with no id collision", seed, peers, clients)
		}
	}
	t.Logf("Valid: %d of %d random configurations pass", pass, n)
	if pass < n*995/1000 {
		t.Fatalf("only %d of %d pass", pass, n)
	}
	ok := []string{"10.0.0.1:2380"}
	okc := []string{"10.0.0.1:2379"}
	for _, c := range [][2][]string{
		{nil, nil}, {ok, nil}, {ok, ok}, {[]string{"10.0.0.1:0"}, okc},
		{[]string{"10.0.0.1:2380", "10.0.0.2:2380"}, []string{"10.0.0.1:2379", "10.0.0.1:2380"}},
	} {
		if Valid(c[0], c[1]) {
			t.Errorf("Valid(%v, %v) = true", c[0], c[1])
		}
	}
	if !Valid(ok, okc) {
		t.Errorf("Valid(%v, %v) = false", ok, okc)
	}
}

// TestName checks the members' names.
func TestName(t *testing.T) {
	if Name(0) != "putgetk-0" || Name(12) != "putgetk-12" {
		t.Fatal(Name(0), Name(12))
	}
}

// round runs one deployment, its configuration from seed (1 to maxK members, random ports, Valid): its member machines and the client's on a network of their own
// (namespaces if netns, else the one loopback address), the members started, then, once every
// member's client address accepts a connection from the client's machine, the client. With faults,
// the network fails from the client's start on (partitions and link faults over every machine; no
// crash: the theorem's machines never crash). It returns the client's result line; a panic, a
// member exiting on its own or a client not done by the deadline fails t.
func round(t *testing.T, i int, netns bool, faults bool, seed uint64) string {
	rng := rand.New(rand.NewPCG(seed, 3))
	k := 1 + rng.IntN(maxK)
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
	for j := 0; j < k; j++ {
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
	var ips []string
	for _, m := range mms {
		ips = append(ips, m.IP)
	}
	peers, clients := randConfig(rng, k, ips)
	if !Valid(peers, clients) {
		t.Fatalf("round %d (seed %d): the configuration %v %v is not Valid", i, seed, peers, clients)
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
	t.Logf("round %d (seed %d, %d members, faults %v): %s; network: %s", i, seed, k, faults, lines[0], r.NetStats())
	if err := r.Err(); err != nil {
		t.Fatalf("round %d: %v (work directory kept: %s)", i, err, work)
	}
	os.RemoveAll(work)
	return lines[0]
}

// TestPutGetK runs putgetK_safe's deployment (notes/putget-dist-plan.md §13): member machines (a random
// configuration per round) and
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
	if l := round(t, 0, netns, false, 0); !strings.HasSuffix(l, "checked") {
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
		if strings.HasSuffix(round(t, i, netns, true, uint64(i)), "checked") {
			checked++
		}
	}
	t.Logf("faulty rounds: %d of %d checked", checked, rounds)
}

// TestNonVacuity is putgetK_safe's non-vacuity over many seeds: for each seed (PUTGETK_SEEDS, default
// 8; -short: 2), a random configuration of 1 to maxK members (seeded), which Valid accepts, run with
// no fault: every member gets past Valid and the client's check (the Put, the Get, the comparison)
// runs ("checked"). Local mode (one loopback address, processes; no namespaces needed). It runs only
// with DIST_RUN set.
func TestNonVacuity(t *testing.T) {
	if os.Getenv("DIST_RUN") == "" {
		t.Skip("set DIST_RUN=1 to run (processes)")
	}
	seeds := 8
	if s := os.Getenv("PUTGETK_SEEDS"); s != "" {
		if v, err := strconv.Atoi(s); err == nil && v > 0 {
			seeds = v
		}
	}
	if testing.Short() {
		seeds = 2
	}
	for seed := 0; seed < seeds; seed++ {
		if l := round(t, seed, false, false, uint64(1000+seed)); !strings.HasSuffix(l, "checked") {
			t.Fatalf("seed %d: the client's check did not run: %q", 1000+seed, l)
		}
	}
}
