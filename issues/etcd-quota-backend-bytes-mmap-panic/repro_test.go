// Reproduction of issues/etcd-quota-backend-bytes-mmap-panic.md.
//
// Copy into server/storage/ of an etcd checkout at the pin (the fork's 249d76bea) or upstream main
// and run
//
//	go test ./storage -run 'TestOpenBackendLargeQuota' -count=1 -v
//
// from server/. OpenBackend runs newBackend on a goroutine whose panic kills the process, so the
// test re-runs itself as a child process and checks the child's output: "panic: failed to open
// database" with bbolt's "mmap too large". The control opens the same kind of directory with the
// default quota.
package storage

import (
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"

	"go.uber.org/zap"

	"go.etcd.io/etcd/server/v3/config"
)

func quotaDataDir(t *testing.T) string {
	dir := t.TempDir()
	if err := os.MkdirAll(filepath.Join(dir, "member", "snap"), 0o700); err != nil {
		t.Fatal(err)
	}
	return dir
}

// TestOpenBackendLargeQuota: a quota of 1 PiB (above bbolt's maxMapSize of 256 TiB on amd64 once
// newBackend adds 10%) makes OpenBackend panic.
func TestOpenBackendLargeQuota(t *testing.T) {
	if dir := os.Getenv("QUOTA_REPRO_CHILD"); dir != "" {
		cfg := config.ServerConfig{Logger: zap.NewExample(), DataDir: dir, QuotaBackendBytes: 1 << 50}
		OpenBackend(cfg, nil)
		return
	}
	cmd := exec.Command(os.Args[0], "-test.run=^TestOpenBackendLargeQuota$")
	cmd.Env = append(os.Environ(), "QUOTA_REPRO_CHILD="+quotaDataDir(t))
	out, err := cmd.CombinedOutput()
	if err == nil {
		t.Fatalf("OpenBackend returned; expected a panic:\n%s", out)
	}
	s := string(out)
	if !strings.Contains(s, "panic: failed to open database") || !strings.Contains(s, "mmap too large") {
		t.Fatalf("unexpected failure (%v):\n%s", err, s)
	}
	t.Logf("the child panicked (%v)", err)
}

// TestOpenBackendDefaultQuota: the control, the same environment with the default quota.
func TestOpenBackendDefaultQuota(t *testing.T) {
	be := OpenBackend(config.ServerConfig{Logger: zap.NewNop(), DataDir: quotaDataDir(t)}, nil)
	if err := be.Close(); err != nil {
		t.Fatal(err)
	}
}
