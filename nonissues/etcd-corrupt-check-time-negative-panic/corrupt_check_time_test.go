// Reproduction of issues/etcd-corrupt-check-time-negative-panic.md: copy into server/embed/ and run
// `go test ./embed -run '^TestNegativeCorruptCheckTimeFlag$'` from server/. It uses the package's
// test helpers newConfigTestURLs and applyTestURLConfig (util_test.go).
package embed

import (
	"flag"
	"os"
	"os/exec"
	"strings"
	"testing"
	"time"
)

// TestNegativeCorruptCheckTimeFlag starts a single-member etcd configured as etcd's command line
// configures it (Config.AddFlags) with --corrupt-check-time=-1s. etcd should either refuse the
// value (StartEtcd returns an error) or run; it should not crash. A panic on a server goroutine
// ends the process, so the server runs in a child process.
func TestNegativeCorruptCheckTimeFlag(t *testing.T) {
	if os.Getenv("CORRUPT_CHECK_CHILD") != "" {
		cfg := NewConfig()
		fs := flag.NewFlagSet("etcd", flag.ContinueOnError)
		cfg.AddFlags(fs)
		if err := fs.Parse([]string{"--corrupt-check-time=-1s"}); err != nil {
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
		time.Sleep(2 * time.Second)
		return
	}
	cmd := exec.Command(os.Args[0], "-test.run=^TestNegativeCorruptCheckTimeFlag$", "-test.v")
	cmd.Env = append(os.Environ(), "CORRUPT_CHECK_CHILD=1")
	out, err := cmd.CombinedOutput()
	if err != nil || strings.Contains(string(out), "panic:") {
		s := string(out)
		if i := strings.Index(s, "panic:"); i >= 0 {
			s = s[i:min(len(s), i+200)]
		}
		t.Fatalf("etcd with --corrupt-check-time=-1s crashed (%v): %s", err, s)
	}
}
