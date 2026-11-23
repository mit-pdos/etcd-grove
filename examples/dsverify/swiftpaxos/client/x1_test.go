package client

import (
	"os"
	"path/filepath"
	"testing"

	"github.com/imdea-software/swiftpaxos/dlog"
)

// X1: findClosest (Connect) must not run `ping` (os/exec is outside the lab's
// model); with equal fixed latencies it picks the first alive replica.
func TestIssueX1_FindClosestNoPing(t *testing.T) {
	dir := t.TempDir()
	marker := filepath.Join(dir, "called")
	script := "#!/bin/sh\n: > " + marker + "\necho 'rtt min/avg/max/mdev = 0.1/0.2/0.3/0.0 ms'\n"
	if err := os.WriteFile(filepath.Join(dir, "ping"), []byte(script), 0755); err != nil {
		t.Fatal(err)
	}
	t.Setenv("PATH", dir)

	c := NewClientLog("", "10.77.0.11", 7001, true, false, false, &dlog.Logger{})
	c.replicas = []string{"10.77.0.12:7002", "10.77.0.13:7003", "10.77.0.14:7004"}
	if err := c.findClosest([]bool{true, true, true}); err != nil {
		t.Fatal(err)
	}
	if _, err := os.Stat(marker); err == nil {
		t.Fatalf("findClosest ran ping")
	}
	if c.ClosestId != 0 {
		t.Fatalf("ClosestId = %d, want 0", c.ClosestId)
	}
}
