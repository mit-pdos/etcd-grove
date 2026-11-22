package dist

import (
	"bytes"
	"fmt"
	"math/rand/v2"
	"os"
	"os/exec"
	"strconv"
	"strings"
	"testing"
	"time"

	"github.com/mit-pdos/etcd-grove/examples/lib/robust"
)

// TestMain runs a member or a client instead of the tests when the test started this binary as
// one (DIST_PROC set: its role and file are the arguments, RunProcess).
func TestMain(m *testing.M) {
	if os.Getenv("DIST_PROC") != "" {
		if err := RunProcess(os.Args[1:]); err != nil {
			fmt.Fprintln(os.Stderr, err)
			os.Exit(2)
		}
		os.Exit(0)
	}
	os.Exit(m.Run())
}

// TestWellFormed checks the deployment predicate's Go mirror on random deployments and on
// ill-formed ones.
func TestWellFormed(t *testing.T) {
	addr := func(i int) (string, string) {
		return fmt.Sprintf("10.77.%d.1:2380", i+1), fmt.Sprintf("10.77.%d.1:2379", i+1)
	}
	for n := 0; n < 200; n++ {
		if _, err := RandomDeployment("wf", 3, addr, ShortSizes); err != nil {
			t.Fatalf("a random deployment is not well formed: %v", err)
		}
	}
	d, _ := RandomDeployment("wf", 3, addr, ShortSizes)
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
	if addrOk("010.1.1.1:80") || addrOk("10.1.1:80") || !addrOk("10.77.1.1:2379") {
		t.Error("addrOk")
	}
}

// wanted says whether d has a workload of a kind DIST_WANT names (comma-separated kind names, e.g.
// auth,authLease), or DIST_WANT is unset: to aim the random deployments at some workloads.
func wanted(d Deployment) bool {
	want := os.Getenv("DIST_WANT")
	if want == "" {
		return true
	}
	for _, w := range d.Workloads {
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
	n, err := NewNet(netns)
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
	tag := fmt.Sprintf("d%d-%d", os.Getpid(), round)
	d, err := RandomDeployment(tag, 3, addr, sz)
	for tries := 0; err == nil && !wanted(d) && tries < 1000; tries++ {
		d, err = RandomDeployment(tag, 3, addr, sz)
	}
	if err != nil {
		t.Fatalf("%v: %v", d, err)
	}
	cfg := Config{Crash: crash, CrashPause: 2 * time.Second, Downtime: time.Second, Netns: netns,
		NetPause: time.Second, NetHold: 2 * time.Second, Deadline: deadline,
		FaultsAtStart: os.Getenv("DIST_FAULTS") == "start", SetupWait: 3 * time.Minute}
	work, err := os.MkdirTemp("", "etcddist-")
	if err != nil {
		t.Fatal(err)
	}
	start := time.Now()
	c, err := Start(d, cfg, Command{Path: exe, Env: []string{"DIST_PROC=1"}}, work, n, ms)
	if err != nil {
		os.RemoveAll(work)
		t.Fatalf("%v: %v", d, err)
	}
	res := c.Run()
	c.Stop()
	t.Logf("round %d: %v (%v)\n  %s; network: %s\n  %s", round, d, time.Since(start).Round(time.Second),
		&c.Stats, c.NetStats(), strings.Join(res.Lines, "\n  "))
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
// Network namespaces need root with CAP_NET_ADMIN: a root without it (a container) runs the test again in a user namespace of its own (robust.RerunInUserns: the bridge variant);
// a non-root runs it again by sudo -n if it can, and in the local mode (one loopback address, no
// network faults) otherwise.
func TestDist(t *testing.T) {
	if os.Getenv("DIST_RUN") == "" {
		t.Skip("set DIST_RUN=1 to run (minutes per deployment; namespaces need root)")
	}
	netns := robust.NetnsAvailable() == nil
	if !netns && os.Getenv("DIST_CHILD") == "" {
		args := []string{"-test.run=^TestDist$", "-test.v", "-test.count=1", "-test.timeout=2h"}
		if testing.Short() {
			args = append(args, "-test.short")
		}
		var rerun func([]string, []string, *bytes.Buffer) error
		if robust.IsRoot() {
			rerun = func(a, e []string, out *bytes.Buffer) error { return robust.RerunInUserns(a, e, out) }
		} else if exec.Command("sudo", "-n", "true").Run() == nil {
			rerun = func(a, e []string, out *bytes.Buffer) error { return robust.RerunAsRoot(a, e, out) }
		}
		if rerun != nil {
			var out bytes.Buffer
			err := rerun(args, []string{"DIST_RUN=1", "DIST_CHILD=1", "DIST_ROUNDS=" + os.Getenv("DIST_ROUNDS"),
				"DIST_FAULTS=" + os.Getenv("DIST_FAULTS"), "DIST_WANT=" + os.Getenv("DIST_WANT"), "DIST_OPS=" + os.Getenv("DIST_OPS")}, &out)
			for _, l := range strings.Split(out.String(), "\n") {
				if strings.TrimSpace(l) != "" {
					t.Log(l)
				}
			}
			if err != nil {
				t.Fatalf("in the namespaces' child: %v", err)
			}
			return
		}
	}
	crash := CrashKill
	if robust.PowerAvailable() == nil {
		crash = CrashMixed
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
