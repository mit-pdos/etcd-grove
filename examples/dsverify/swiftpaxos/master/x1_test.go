package master

import (
	"os"
	"path/filepath"
	"testing"

	"github.com/imdea-software/swiftpaxos/config"
	"github.com/imdea-software/swiftpaxos/dlog"
	"github.com/imdea-software/swiftpaxos/replica/defs"
)

// fakePing puts a `ping` on an otherwise empty PATH that records each call
// and prints a valid summary line, and returns the marker file's path.
func fakePing(t *testing.T) string {
	dir := t.TempDir()
	marker := filepath.Join(dir, "called")
	script := "#!/bin/sh\n: > " + marker + "\necho 'rtt min/avg/max/mdev = 0.1/0.2/0.3/0.0 ms'\n"
	if err := os.WriteFile(filepath.Join(dir, "ping"), []byte(script), 0755); err != nil {
		t.Fatal(err)
	}
	t.Setenv("PATH", dir)
	return marker
}

// X1: Register must not run `ping` (os/exec is outside the lab's model) and
// must still choose a leader, deterministically (all latencies equal: index 0).
func TestIssueX1_RegisterNoPing(t *testing.T) {
	marker := fakePing(t)
	m := New(3, 7001, &config.Config{}, &dlog.Logger{})
	addrs := []string{"10.77.0.12", "10.77.0.13", "10.77.0.14"}
	var last defs.RegisterReply
	for _, a := range addrs {
		last = defs.RegisterReply{}
		if err := m.Register(&defs.RegisterArgs{Addr: a, Port: 7000}, &last); err != nil {
			t.Fatal(err)
		}
	}
	if !last.Ready {
		t.Fatalf("not ready after %d registrations", len(addrs))
	}
	if _, err := os.Stat(marker); err == nil {
		t.Fatalf("Register ran ping")
	}
	// A replica registers until Ready: each one's second call says whether it leads.
	for i, a := range addrs {
		var r defs.RegisterReply
		if err := m.Register(&defs.RegisterArgs{Addr: a, Port: 7000}, &r); err != nil {
			t.Fatal(err)
		}
		if !r.Ready || r.ReplicaId != i || r.IsLeader != (i == 0) {
			t.Fatalf("replica %d: reply %+v, want ready, leader only for 0", i, r)
		}
	}
}
