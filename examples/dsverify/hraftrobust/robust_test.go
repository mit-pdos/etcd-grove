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
// DIR (go tool covdata); HRAFTNET_WARM=MS (passed to the machines) makes the orchestrator
// hraftnet.WarmOrch(MS), the admin alone for MS first. Rounds: HRAFTROBUST_ROUNDS (default 2).
package hraftrobust

import (
	"os"
	"os/exec"
	"path/filepath"
	"strconv"
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
	if w := os.Getenv("HRAFTNET_WARM"); w != "" {
		env = append(env, "HRAFTNET_WARM="+w)
	}
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
		"HRAFTNET_WARM=" + os.Getenv("HRAFTNET_WARM"), "HRAFTROBUST_PAUSE_MS=" + os.Getenv("HRAFTROBUST_PAUSE_MS"),
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
