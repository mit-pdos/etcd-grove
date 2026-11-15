package driver

import (
	"fmt"
	"os"
	"testing"

	"github.com/anishathalye/porcupine"
	"github.com/mit-pdos/etcd-grove/examples/lib/lintest"
	"github.com/mit-pdos/etcd-grove/examples/raft/kvnet"
)

// TestMain runs a replica instead of the tests when the driver started this binary as one
// (KVNET_NODE set: the replicas are processes of the test binary itself).
func TestMain(m *testing.M) {
	if os.Getenv("KVNET_NODE") != "" {
		cfg, err := kvnet.ParseNodeArgs(os.Args[1:])
		if err != nil {
			fmt.Fprintln(os.Stderr, err)
			os.Exit(2)
		}
		kvnet.RunNode(cfg)
	}
	os.Exit(m.Run())
}

// self starts replicas as processes of this test binary.
func self(t *testing.T) Command {
	exe, err := os.Executable()
	if err != nil {
		t.Fatal(err)
	}
	return Command{Path: exe, Env: []string{"KVNET_NODE=1"}}
}

// round runs one round of crash mode crash and fails t unless porcupine answers Ok and nothing
// else failed.
func round(t *testing.T, crash string) {
	cfg := RandomConfig(crash)
	if testing.Short() {
		cfg.Clients, cfg.Ops = 3, 30
	}
	res, c := Run(cfg, self(t), t.TempDir(), lintest.CounterClock())
	if c == nil {
		t.Fatal(res.Err)
	}
	var dump string
	if res.Err != nil || res.Check != porcupine.Ok {
		dump = c.Dump()
	}
	c.Stop()
	t.Logf("%+v, %d proposers, %d x %d operations: %v\n  %v", cfg.Options, cfg.Proposers, cfg.Clients, cfg.Ops, res.Check, &c.Stats)
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
	round(t, CrashKill)
}

// TestPower runs a round whose crashes are kills and power losses, every replica on a disk of
// its own. It needs sudo without a password, and runs only with KVNET_POWER set (it makes loop
// and device-mapper devices as root).
func TestPower(t *testing.T) {
	if os.Getenv("KVNET_POWER") == "" {
		t.Skip("set KVNET_POWER=1 to run (needs sudo: loop and dm-flakey devices)")
	}
	if err := PowerAvailable(); err != nil {
		t.Skip("power losses unavailable:", err)
	}
	round(t, CrashMixed)
}
