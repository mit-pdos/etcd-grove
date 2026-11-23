package master

import (
	"fmt"
	"os"
	"path/filepath"
	"testing"

	"github.com/imdea-software/swiftpaxos-epaxos/config"
	"github.com/imdea-software/swiftpaxos-epaxos/dlog"
	"github.com/imdea-software/swiftpaxos-epaxos/replica/defs"
)

// TestRegisterRunsNoProgram registers five replicas with a master configured as the kit's
// (no leader in the configuration), with a `ping` program on PATH that records its run and
// prints no ping summary. Register must not run an external program (os/exec is outside the
// system's model, X1), and the replica told it is the leader is replica 0 (every latency 0).
func TestRegisterRunsNoProgram(t *testing.T) {
	dir := t.TempDir()
	marker := filepath.Join(dir, "ran")
	script := "#!/bin/sh\ntouch " + marker + "\necho no summary\n"
	if err := os.WriteFile(filepath.Join(dir, "ping"), []byte(script), 0o755); err != nil {
		t.Fatal(err)
	}
	t.Setenv("PATH", dir)

	m := New(5, 7001, &config.Config{Proxy: &config.ProxyInfo{}}, &dlog.Logger{})
	for round := 0; round < 2; round++ {
		for i := 0; i < 5; i++ {
			var reply defs.RegisterReply
			args := &defs.RegisterArgs{Addr: fmt.Sprintf("10.77.0.1%d", i+2), Port: 7002 + i}
			if err := m.Register(args, &reply); err != nil {
				t.Fatal(err)
			}
			if round == 1 && (!reply.Ready || reply.ReplicaId != i || reply.IsLeader != (i == 0)) {
				t.Fatalf("replica %d: reply %+v", i, reply)
			}
		}
	}
	if _, err := os.Stat(marker); err == nil {
		t.Fatal("Register ran the ping program")
	}
}
