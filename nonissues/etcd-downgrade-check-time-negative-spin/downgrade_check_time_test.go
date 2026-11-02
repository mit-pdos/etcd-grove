//go:build linux

// Reproduction of issues/etcd-downgrade-check-time-negative-spin.md: copy into server/embed/ and
// run `go test ./embed -run '^TestNegativeDowngradeCheckTimeFlag$'` from server/. It uses the
// package's test helpers newConfigTestURLs and applyTestURLConfig (util_test.go), and getrusage
// (Linux) to measure the process's CPU time.
package embed

import (
	"flag"
	"syscall"
	"testing"
	"time"
)

func downgradeTestCPUTime(t *testing.T) time.Duration {
	var ru syscall.Rusage
	if err := syscall.Getrusage(syscall.RUSAGE_SELF, &ru); err != nil {
		t.Fatal(err)
	}
	return time.Duration(ru.Utime.Nano() + ru.Stime.Nano())
}

// TestNegativeDowngradeCheckTimeFlag starts a single-member etcd configured as etcd's command line
// configures it (Config.AddFlags) with --downgrade-check-time=-1s, and measures the CPU time the
// idle member uses over two seconds. etcd should either refuse the value (StartEtcd returns an
// error) or run idle; it should not keep a core busy.
func TestNegativeDowngradeCheckTimeFlag(t *testing.T) {
	cfg := NewConfig()
	fs := flag.NewFlagSet("etcd", flag.ContinueOnError)
	cfg.AddFlags(fs)
	if err := fs.Parse([]string{"--downgrade-check-time=-1s"}); err != nil {
		t.Fatal(err)
	}
	applyTestURLConfig(cfg, newConfigTestURLs())
	cfg.Dir = t.TempDir()
	e, err := StartEtcd(cfg)
	if err != nil {
		t.Logf("StartEtcd refused the configuration: %v", err)
		return
	}
	defer e.Close()
	select {
	case <-e.Server.ReadyNotify():
	case <-time.After(10 * time.Second):
		t.Fatal("server not ready")
	}
	time.Sleep(time.Second) // past startup

	const wall = 2 * time.Second
	before := downgradeTestCPUTime(t)
	time.Sleep(wall)
	used := downgradeTestCPUTime(t) - before
	t.Logf("CPU time of the idle member over %v: %v", wall, used)
	if used > wall/2 {
		t.Errorf("an idle member with --downgrade-check-time=-1s used %v of CPU in %v", used, wall)
	}
}
