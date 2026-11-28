// Package hraftrobust runs the hraft kit's deployment (examples/dsverify/hraft/examples/hraftnet,
// notes/dsv-hraft.md) the way the theorem's machines run: twelve processes, each machine a network
// namespace of its own at the kit's address (examples/lib/robust: machine k at 10.77.k.1, servers
// 1..6, clients 0..4, then the orchestrator), with the network faults the kernel makes in the
// router (partitions, one way or both, dropped or refused; delay, loss, duplication and reordering
// of packets) from the start. No machine crashes (the statement's are machines that never do).
// A machine is the kit's covmachine binary (`covmachine <name>`: the machine's program, Server,
// Client or Orch, unchanged); the orchestrator panics if porcupine rejects the history, which fails
// the run.
//
// It is the coverage run of the kit (notes/dsv-hraft.md, "Coverage"): with HRAFTROBUST_COVER=DIR,
// the binary is built with -cover over the raft package and every machine writes its counters into
// DIR (go tool covdata). The orchestrator is hraftnet.WarmOrch(HRAFTNET_WARM, HRAFTNET_OPS): the
// admin alone for HRAFTNET_WARM ms first (default 1), HRAFTNET_OPS operations per client (default
// 8; Orch itself draws 1 to MaxOps). Rounds: HRAFTROBUST_ROUNDS (default 2).
package hraftrobust

import (
	"os"
	"os/exec"
	"path/filepath"
	"strconv"
	"strings"
	"testing"
	"time"

	"github.com/mit-pdos/etcd-grove/examples/lib/robust"
)

// names is the machines' names, in the kit's order of addresses.
func names() []string {
	var ns []string
	for s := 1; s <= 6; s++ {
		ns = append(ns, "server"+strconv.Itoa(s))
	}
	for c := 0; c < 5; c++ {
		ns = append(ns, "client"+strconv.Itoa(c))
	}
	return append(ns, "orch")
}

// build builds the kit's covmachine into dir (with coverage of the raft package if cover).
func build(t *testing.T, dir string, cover bool) string {
	kit, err := filepath.Abs("../hraft")
	if err != nil {
		t.Fatal(err)
	}
	bin := filepath.Join(dir, "covmachine")
	args := []string{"build", "-tags", "covmachine", "-o", bin}
	if cover {
		args = append(args, "-cover", "-covermode=atomic", "-coverpkg=github.com/hashicorp/raft,github.com/hashicorp/raft/examples/hraftnet/covmachine")
	}
	cmd := exec.Command("go", append(args, "./examples/hraftnet/covmachine")...)
	cmd.Dir = kit
	cmd.Env = append(os.Environ(), "GOWORK=off")
	if out, err := cmd.CombinedOutput(); err != nil {
		t.Fatalf("building the kit: %v\n%s", err, out)
	}
	return bin
}

// envMs is the variable name's value in ms (the faults' mean pause HRAFTROBUST_PAUSE_MS, their mean
// duration HRAFTROBUST_HOLD_MS), def if unset.
func envMs(name string, def int) time.Duration {
	if v, err := strconv.Atoi(os.Getenv(name)); err == nil && v > 0 {
		return time.Duration(v) * time.Millisecond
	}
	return time.Duration(def) * time.Millisecond
}

// round runs the deployment once, with the network faults from the start.
func round(t *testing.T, i int, bin string, cover string) {
	n, err := robust.NewNetwork("hrf" + strconv.Itoa(os.Getpid()%10000))
	if err != nil {
		t.Fatal(err)
	}
	defer n.Close()
	var ms []*robust.Machine
	for _, name := range names() {
		m, err := n.AddMachine(name)
		if err != nil {
			t.Fatal(err)
		}
		ms = append(ms, m)
	}
	work, err := os.MkdirTemp("", "hraftrobust-")
	if err != nil {
		t.Fatal(err)
	}
	var env []string
	if cover != "" {
		env = append(env, "GOCOVERDIR="+cover)
	}
	// the orchestrator is always hraftnet.WarmOrch: Orch draws up to MaxOps operations per client,
	// and a run pins a small number (HRAFTNET_OPS, default 8) and the admin's head start
	// (HRAFTNET_WARM, default 1 ms)
	w := os.Getenv("HRAFTNET_WARM")
	if w == "" {
		w = "1"
	}
	env = append(env, "HRAFTNET_WARM="+w, "HRAFTNET_OPS="+os.Getenv("HRAFTNET_OPS"))
	cfg := robust.Config{Crash: robust.CrashKill, Netns: true, Deadline: 10 * time.Minute, FaultsAtStart: true,
		NetPause: envMs("HRAFTROBUST_PAUSE_MS", 300), NetHold: envMs("HRAFTROBUST_HOLD_MS", 1000)}
	r, err := robust.NewRun(cfg, robust.Command{Path: bin, Env: env}, n, work)
	if err != nil {
		t.Fatal(err)
	}
	defer r.Stop()
	var nodes []robust.Client
	for k, name := range names()[:11] {
		nodes = append(nodes, robust.Client{Name: name, Machine: ms[k], Args: []string{name}})
	}
	orch := []robust.Client{{Name: "orch", Machine: ms[11], Args: []string{"orch"}}}
	t0 := time.Now()
	r.RunClients(nodes, orch, ms)
	t.Logf("round %d: %v; network: %s", i, time.Since(t0).Round(time.Second), r.NetStats())
	if err := r.Err(); err != nil {
		t.Fatalf("round %d: %v (logs kept in %s)", i, err, work)
	}
	os.RemoveAll(work)
}

// TestRobust runs HRAFTROBUST_ROUNDS rounds (network namespaces: root, or user namespaces through
// robust.RerunTest). Set HRAFTROBUST_RUN=1 to run it.
func TestRobust(t *testing.T) {
	if os.Getenv("HRAFTROBUST_RUN") == "" {
		t.Skip("set HRAFTROBUST_RUN=1 to run (processes and network namespaces)")
	}
	if robust.RerunTest(t, "TestRobust", "120m", testing.Short(), []string{"HRAFTROBUST_RUN=1",
		"HRAFTROBUST_ROUNDS=" + os.Getenv("HRAFTROBUST_ROUNDS"), "HRAFTROBUST_COVER=" + os.Getenv("HRAFTROBUST_COVER"),
		"HRAFTNET_WARM=" + os.Getenv("HRAFTNET_WARM"), "HRAFTNET_OPS=" + os.Getenv("HRAFTNET_OPS"), "HRAFTROBUST_PAUSE_MS=" + os.Getenv("HRAFTROBUST_PAUSE_MS"),
		"HRAFTROBUST_HOLD_MS=" + os.Getenv("HRAFTROBUST_HOLD_MS")}) {
		return
	}
	if err := robust.NetnsAvailable(); err != nil {
		t.Skipf("no network namespaces: %v", err)
	}
	rounds := 2
	if v, err := strconv.Atoi(os.Getenv("HRAFTROBUST_ROUNDS")); err == nil && v > 0 {
		rounds = v
	}
	cover := os.Getenv("HRAFTROBUST_COVER")
	bin := build(t, t.TempDir(), cover != "")
	for i := 0; i < rounds; i++ {
		round(t, i, bin, cover)
	}
}

// roundCrash runs the crash deployment once (hraft_robust): the servers are the restartable
// machines (`covmachine rserver<id> DIR`, rserver.ServerR over its data directory DIR, a directory
// of its own, or its disk's mount in the power modes), each in a group of its own, so that any
// number of them may be down at once; each is killed (SIGKILL) at random and restarted after a
// random downtime, its filesystem synced (kill) or its disk's power lost (power), per
// HRAFTROBUST_CRASH (kill, power or mixed; default kill). The clients and the orchestrator never
// crash. The network faults are round's. Each server's log starts every incarnation with what its
// directory held (disk.Describe).
func roundCrash(t *testing.T, i int, bin string, cover string) {
	n, err := robust.NewNetwork("hrc" + strconv.Itoa(os.Getpid()%10000))
	if err != nil {
		t.Fatal(err)
	}
	defer n.Close()
	var ms []*robust.Machine
	for _, name := range names() {
		m, err := n.AddMachine(name)
		if err != nil {
			t.Fatal(err)
		}
		ms = append(ms, m)
	}
	work, err := os.MkdirTemp("", "hraftrobustcrash-")
	if err != nil {
		t.Fatal(err)
	}
	var env []string
	if cover != "" {
		env = append(env, "GOCOVERDIR="+cover)
	}
	w := os.Getenv("HRAFTNET_WARM")
	if w == "" {
		w = "1"
	}
	env = append(env, "HRAFTNET_WARM="+w, "HRAFTNET_OPS="+os.Getenv("HRAFTNET_OPS"))
	mode := os.Getenv("HRAFTROBUST_CRASH")
	if mode == "" {
		mode = robust.CrashKill
	}
	cfg := robust.Config{Crash: mode, CrashPause: envMs("HRAFTROBUST_CRASH_MS", 1500),
		Downtime: envMs("HRAFTROBUST_DOWN_MS", 2000), Netns: true, Deadline: 10 * time.Minute, FaultsAtStart: true,
		NetPause: envMs("HRAFTROBUST_PAUSE_MS", 300), NetHold: envMs("HRAFTROBUST_HOLD_MS", 1000)}
	r, err := robust.NewRun(cfg, robust.Command{Path: bin, Env: env}, n, work)
	if err != nil {
		t.Fatal(err)
	}
	defer r.Stop()
	var groups []*robust.Group
	for k := 0; k < 6; k++ {
		g := r.NewGroup()
		rs, err := g.Add(names()[k], ms[k])
		if err != nil {
			t.Fatal(err)
		}
		rs.Args = []string{"r" + names()[k], rs.Dir}
		groups = append(groups, g)
	}
	for _, g := range groups {
		if err := g.Start(); err != nil {
			t.Fatal(err)
		}
	}
	var nodes []robust.Client
	for k, name := range names()[6:11] {
		nodes = append(nodes, robust.Client{Name: name, Machine: ms[6+k], Args: []string{name}})
	}
	orch := []robust.Client{{Name: "orch", Machine: ms[11], Args: []string{"orch"}}}
	t0 := time.Now()
	r.RunClients(nodes, orch, ms)
	t.Logf("round %d: %v; crashes: %s; network: %s", i, time.Since(t0).Round(time.Second), r.Stats.String(), r.NetStats())
	for k := 0; k < 6; k++ {
		t.Logf("round %d, %s's incarnations:\n%s", i, names()[k], starts(r.LogPath(names()[k])))
	}
	if err := r.Err(); err != nil {
		t.Fatalf("round %d: %v (logs kept in %s)", i, err, work)
	}
	if os.Getenv("HRAFTROBUST_KEEP") == "" {
		os.RemoveAll(work)
	}
}

// starts is the lines of the log path that say what a server's directory held as it started.
func starts(path string) string {
	b, err := os.ReadFile(path)
	if err != nil {
		return err.Error()
	}
	out := ""
	for _, l := range strings.Split(string(b), "\n") {
		if strings.HasPrefix(l, "covmachine: ") {
			out += "  " + l + "\n"
		}
	}
	return out
}

// TestRobustCrash runs HRAFTROBUST_ROUNDS rounds of the crash deployment (roundCrash). Set
// HRAFTROBUST_RUN=1 to run it.
func TestRobustCrash(t *testing.T) {
	if os.Getenv("HRAFTROBUST_RUN") == "" {
		t.Skip("set HRAFTROBUST_RUN=1 to run (processes and network namespaces)")
	}
	if robust.RerunTest(t, "TestRobustCrash", "120m", testing.Short(), []string{"HRAFTROBUST_RUN=1",
		"HRAFTROBUST_ROUNDS=" + os.Getenv("HRAFTROBUST_ROUNDS"), "HRAFTROBUST_COVER=" + os.Getenv("HRAFTROBUST_COVER"),
		"HRAFTNET_WARM=" + os.Getenv("HRAFTNET_WARM"), "HRAFTNET_OPS=" + os.Getenv("HRAFTNET_OPS"),
		"HRAFTROBUST_PAUSE_MS=" + os.Getenv("HRAFTROBUST_PAUSE_MS"), "HRAFTROBUST_HOLD_MS=" + os.Getenv("HRAFTROBUST_HOLD_MS"),
		"HRAFTROBUST_CRASH=" + os.Getenv("HRAFTROBUST_CRASH"), "HRAFTROBUST_CRASH_MS=" + os.Getenv("HRAFTROBUST_CRASH_MS"),
		"HRAFTROBUST_DOWN_MS=" + os.Getenv("HRAFTROBUST_DOWN_MS"), "HRAFTROBUST_KEEP=" + os.Getenv("HRAFTROBUST_KEEP")}) {
		return
	}
	if err := robust.NetnsAvailable(); err != nil {
		t.Skipf("no network namespaces: %v", err)
	}
	rounds := 2
	if v, err := strconv.Atoi(os.Getenv("HRAFTROBUST_ROUNDS")); err == nil && v > 0 {
		rounds = v
	}
	cover := os.Getenv("HRAFTROBUST_COVER")
	bin := build(t, t.TempDir(), cover != "")
	for i := 0; i < rounds; i++ {
		roundCrash(t, i, bin, cover)
	}
}
