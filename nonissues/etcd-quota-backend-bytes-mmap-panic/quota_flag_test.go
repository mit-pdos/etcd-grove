// Reproduction of issues/etcd-quota-backend-bytes-mmap-panic.md: copy into server/embed/ and run
// `go test ./embed -run '^TestLargeQuotaBackendBytesFlag$'` from server/. It uses the package's
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

// TestLargeQuotaBackendBytesFlag starts a single-member etcd configured as etcd's command line
// configures it (Config.AddFlags) with --quota-backend-bytes=1125899906842624 (1 PiB). etcd should
// either refuse the value (StartEtcd returns an error) or run; it should not crash. A panic while
// the backend is opened ends the process, so the server runs in a child process.
func TestLargeQuotaBackendBytesFlag(t *testing.T) {
	if os.Getenv("QUOTA_FLAG_CHILD") != "" {
		cfg := NewConfig()
		fs := flag.NewFlagSet("etcd", flag.ContinueOnError)
		cfg.AddFlags(fs)
		if err := fs.Parse([]string{"--quota-backend-bytes=1125899906842624"}); err != nil {
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
		return
	}
	cmd := exec.Command(os.Args[0], "-test.run=^TestLargeQuotaBackendBytesFlag$", "-test.v")
	cmd.Env = append(os.Environ(), "QUOTA_FLAG_CHILD=1")
	out, err := cmd.CombinedOutput()
	if err != nil || strings.Contains(string(out), "panic:") {
		s := string(out)
		if i := strings.Index(s, "panic:"); i >= 0 {
			s = s[i:min(len(s), i+300)]
		}
		t.Fatalf("etcd with --quota-backend-bytes=1125899906842624 crashed (%v): %s", err, s)
	}
}
