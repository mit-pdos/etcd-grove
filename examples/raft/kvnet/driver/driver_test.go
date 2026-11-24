package driver

import (
	"bytes"
	"fmt"
	"os"
	"strings"
	"testing"

	"github.com/anishathalye/porcupine"
	"github.com/mit-pdos/etcd-grove/examples/lib/robust"
	"github.com/mit-pdos/etcd-grove/examples/raft/kvnet"
)

// TestMain runs a replica or the checking client instead of the tests when the harness started
// this binary as one (KVNET_PROC set: the processes are of the test binary itself, their role
// and flags the arguments, RunProcess).
func TestMain(m *testing.M) {
	if os.Getenv("KVNET_PROC") != "" {
		if err := RunProcess(os.Args[1:]); err != nil {
			fmt.Fprintln(os.Stderr, err)
			os.Exit(2)
		}
		os.Exit(0)
	}
	os.Exit(m.Run())
}

// self starts the harness's processes as processes of this test binary.
func self(t *testing.T) Command {
	exe, err := os.Executable()
	if err != nil {
		t.Fatal(err)
	}
	return Command{Path: exe, Env: []string{"KVNET_PROC=1"}}
}

// round runs one round of crash mode crash (with the network's faults if netns) and fails t
// unless porcupine answers Ok and nothing else failed.
func round(t *testing.T, crash string, netns bool) {
	cfg := RandomConfig(crash, netns)
	res, c := Run(cfg, self(t), t.TempDir())
	if c == nil {
		t.Fatal(res.Err)
	}
	var dump string
	if res.Err != nil || res.Check != porcupine.Ok {
		dump = c.Dump()
	}
	c.Stop()
	t.Logf("%+v: %v\n  %v\n  network: %s", cfg.Options, res.Check, &c.Stats, c.NetStats())
	if res.Err != nil {
		t.Fatalf("%v\n%s", res.Err, dump)
	}
	if res.Check != porcupine.Ok {
		t.Fatalf("porcupine answered %v\n%s", res.Check, dump)
	}
}

// TestKill runs a round whose crashes are kills (SIGKILL, then a sync of the replica's
// filesystem).
func TestKill(t *testing.T) {
	round(t, CrashKill, false)
}

// TestPower runs a round whose crashes are kills and power losses, every replica on a disk of
// its own. It needs sudo without a password, and runs only with KVNET_POWER set (it makes loop
// and device-mapper devices as root).
func TestPower(t *testing.T) {
	if os.Getenv("KVNET_POWER") == "" {
		t.Skip("set KVNET_POWER=1 to run (needs sudo: loop and dm-flakey devices)")
	}
	if err := robust.PowerAvailable(); err != nil {
		t.Skip("power losses unavailable:", err)
	}
	round(t, CrashMixed, false)
}

// TestNetns runs a round on machines that are network namespaces, with the network's faults
// (partitions, resets, delay, loss, duplication, reordering) and kills and power losses. It needs
// sudo without a password, and runs only with KVNET_NETNS set: the test binary runs again as root
// (robust.RerunAsRoot), and the replicas run as root in their namespaces.
func TestNetns(t *testing.T) {
	if os.Getenv("KVNET_NETNS") == "" {
		t.Skip("set KVNET_NETNS=1 to run (needs sudo: network namespaces, iptables, tc, disks)")
	}
	if !robust.IsRoot() {
		var out bytes.Buffer
		args := []string{"-test.run=^TestNetns$", "-test.v", "-test.count=1", "-test.timeout=20m"}
		if testing.Short() {
			args = append(args, "-test.short")
		}
		err := robust.RerunAsRoot(args, []string{"KVNET_NETNS=1"}, &out)
		for _, l := range strings.Split(out.String(), "\n") {
			if strings.TrimSpace(l) != "" {
				t.Log(l)
			}
		}
		if err != nil {
			t.Fatalf("as root: %v", err)
		}
		return
	}
	if err := robust.NetnsAvailable(); err != nil {
		t.Skip("network namespaces unavailable:", err)
	}
	crash := CrashKill
	if robust.PowerAvailable() == nil {
		crash = CrashMixed
	}
	round(t, crash, true)
}

// TestRestartsInProcess runs rounds of random configurations (kills as crashes) and checks that
// in each the replicas were restarted in their processes (kvcheck's ReqDisrupt restart: raft's
// Node.Stop, then RestartNode in the same process) and porcupine still answers Ok: the clean
// stop-and-restart path runs alongside the machines' crashes, over many random runs.
func TestRestartsInProcess(t *testing.T) {
	rounds := 4
	if testing.Short() {
		rounds = 1
	}
	for i := 0; i < rounds; i++ {
		cfg := RandomConfig(CrashKill, false)
		res, c := Run(cfg, self(t), t.TempDir())
		if c == nil {
			t.Fatal(res.Err)
		}
		c.Stop()
		n := c.Stats.Node[kvnet.StRestartsInProcess]
		t.Logf("round %d %+v: %v; restarts in process %d, kills %d", i, cfg.Options, res.Check, n, c.Stats.Kills.Load())
		if res.Err != nil {
			t.Fatal(res.Err)
		}
		if res.Check != porcupine.Ok {
			t.Fatalf("round %d: porcupine answered %v", i, res.Check)
		}
		if n == 0 {
			t.Fatalf("round %d: no replica was restarted in its process", i)
		}
	}
}
