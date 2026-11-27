package putget

import (
	"fmt"
	"math/rand/v2"
	"os"
	"path/filepath"
	"strconv"
	"strings"
	"testing"
	"time"

	"github.com/mit-pdos/etcd-grove/examples/lib/etcdstart"
	"github.com/mit-pdos/etcd-grove/examples/lib/robust"
)

// TestMain runs the member or the client instead of the tests when the test started this binary
// as one (PUTGET_PROC set; the arguments: "member" PEER CLIENT, or "client" CLIENT): what
// cmd/member and cmd/client do, for a binary that is both (the test binary).
func TestMain(m *testing.M) {
	if os.Getenv("PUTGET_PROC") != "" {
		a := os.Args[1:]
		switch {
		case len(a) == 3 && a[0] == "member":
			Member(a[1], a[2])
			fmt.Fprintln(os.Stderr, "member: a step failed")
			os.Exit(1)
		case len(a) == 2 && a[0] == "client":
			if Client(a[1]) {
				fmt.Println("putget: checked")
			} else {
				fmt.Println("putget: ended")
			}
			os.Exit(0)
		}
		fmt.Fprintln(os.Stderr, "usage: member PEER CLIENT | client CLIENT")
		os.Exit(2)
	}
	// The machines inherit this process's environment: give them the one the theorems' premises
	// describe (verifyEnvOff: ETCD_VERIFY off; no proxy variable set, so that no non-loopback
	// dial or request goes through a proxy: examples/premisefix/proxyenv).
	for _, k := range []string{"ETCD_VERIFY", "HTTP_PROXY", "http_proxy", "HTTPS_PROXY", "https_proxy", "NO_PROXY", "no_proxy"} {
		os.Unsetenv(k)
	}
	os.Exit(m.Run())
}

// round runs one deployment: the member's machine and the client's on a network of their own
// (namespaces if netns, else the one loopback address), the member started, then, once its client
// address accepts a connection from the client's machine, the client. With faults, the network
// fails from the client's start on (partitions and link faults over both machines; no crash: the
// interim theorem's machines never crash). It returns the client's result line; a panic, a member
// exiting on its own or a client not done by the deadline fails t.
func round(t *testing.T, i int, netns bool, faults bool) string {
	exe, err := os.Executable()
	if err != nil {
		t.Fatal(err)
	}
	n, err := robust.NewNetworkOrLocal(netns, "pg")
	if err != nil {
		t.Fatal(err)
	}
	defer n.Close()
	mm, err := n.AddMachine("member")
	if err != nil {
		t.Fatal(err)
	}
	cm, err := n.AddMachine("client")
	if err != nil {
		t.Fatal(err)
	}
	peer, client := mm.IP+":2380", mm.IP+":2379"
	if !n.Namespaces() {
		base := 21000 + 2*rand.IntN(4000)
		peer, client = mm.IP+":"+strconv.Itoa(base), mm.IP+":"+strconv.Itoa(base+1)
	}
	cfg := robust.Config{Crash: robust.CrashKill, Netns: netns, Deadline: 2 * time.Minute,
		FaultsAtStart: true, SetupWait: time.Minute}
	if faults {
		cfg.NetPause, cfg.NetHold = 300*time.Millisecond, time.Second
	}
	work, err := os.MkdirTemp("", "putgetdist-")
	if err != nil {
		t.Fatal(err)
	}
	r, err := robust.NewRun(cfg, robust.Command{Path: exe, Env: []string{"PUTGET_PROC=1"}}, n, work)
	if err != nil {
		t.Fatal(err)
	}
	defer r.Stop()
	// the member's data directory and WAL area: empty directories of its own, at the paths
	// etcdstart.StartServer uses (the theorem's ServerStart)
	g := r.NewGroup()
	mb, err := g.Add(Name, mm)
	if err != nil {
		t.Fatal(err)
	}
	links := []string{filepath.Join(etcdstart.DataBase, Name+".etcd"), filepath.Join(etcdstart.WALBase, Name+".etcd")}
	for j, sub := range []string{"data", "wal"} {
		if err := os.MkdirAll(filepath.Join(mb.Dir, sub), 0o755); err != nil {
			t.Fatal(err)
		}
		if err := robust.Symlink(filepath.Join(mb.Dir, sub), links[j]); err != nil {
			t.Fatal(err)
		}
		defer os.Remove(links[j])
	}
	mb.Args = []string{"member", peer, client}
	if err := g.Start(); err != nil {
		t.Fatal(err)
	}
	// a liveness wait only (the test's, not the program's): the member's listener is up
	up := false
	for k := 0; k < 300 && r.Err() == nil; k++ {
		if c, err := cm.Dial(client, time.Second); err == nil {
			c.Close()
			up = true
			break
		}
		time.Sleep(100 * time.Millisecond)
	}
	if !up {
		t.Fatalf("round %d: the member's client address %s never accepted (%v); its log:\n%s", i, client,
			r.Err(), robust.Tail(r.LogPath(Name), 40))
	}
	lines := r.RunClients(nil, []robust.Client{{Name: "client", Machine: cm, Args: []string{"client", client},
		Ready: filepath.Join(work, "client.ready")}}, []*robust.Machine{mm, cm})
	t.Logf("round %d (faults %v): %s; network: %s", i, faults, lines[0], r.NetStats())
	if err := r.Err(); err != nil {
		t.Fatalf("round %d: %v (work directory kept: %s)", i, err, work)
	}
	os.RemoveAll(work)
	return lines[0]
}

// TestPutGet runs putget_safe's deployment (notes/putget-dist-plan.md): one member machine, one
// client machine, no crash. The first round has no fault and must check; the others (PUTGET_ROUNDS,
// default 4; -short: 1) have network faults on namespaces from the client's start, where the check
// runs or a step fails, and nothing panics. It runs only with DIST_RUN set (it makes processes, and
// network namespaces where it can: robust.RerunTest, as examples/etcd/dist's TestDist).
func TestPutGet(t *testing.T) {
	if os.Getenv("DIST_RUN") == "" {
		t.Skip("set DIST_RUN=1 to run (processes; namespaces need root)")
	}
	if robust.RerunTest(t, "TestPutGet", "30m", testing.Short(), []string{"DIST_RUN=1",
		"PUTGET_ROUNDS=" + os.Getenv("PUTGET_ROUNDS")}) {
		return
	}
	netns := robust.NetnsAvailable() == nil
	if l := round(t, 0, netns, false); !strings.HasSuffix(l, "checked") {
		t.Fatalf("the fault-free round did not check: %q", l)
	}
	rounds := 4
	if s := os.Getenv("PUTGET_ROUNDS"); s != "" {
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

// TestAddrOk: the addresses TestPutGet deploys at pass Member's and Client's check (so its
// fault-free round reaches the real path), and malformed ones do not (Member and Client then
// return at once).
func TestAddrOk(t *testing.T) {
	for _, a := range []string{"10.0.0.1:2380", "10.0.0.1:2379", "127.0.0.1:21000", "127.0.0.1:28999"} {
		if !AddrOk(a) {
			t.Errorf("AddrOk(%q) = false", a)
		}
	}
	for _, a := range []string{"", "localhost:2379", "0.1.2.3:80", "224.0.0.1:80", "1.2.3.4:0",
		"1.2.3.4:40000", "01.2.3.4:80", "1.2.3:80", "1.2.3.4.5:80", "1.2.3.4", "256.1.1.1:80"} {
		if AddrOk(a) {
			t.Errorf("AddrOk(%q) = true", a)
		}
	}
	Member("bad", "10.0.0.1:2379")           // returns at once
	Member("10.0.0.1:2379", "10.0.0.1:2379") // the same address twice: returns at once
	if Client("bad") {
		t.Error("Client(\"bad\") ran its check")
	}
}
