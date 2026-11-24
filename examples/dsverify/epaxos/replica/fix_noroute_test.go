package replica

import (
	"os"
	"os/exec"
	"testing"

	"github.com/imdea-software/swiftpaxos-epaxos/config"
	"github.com/imdea-software/swiftpaxos-epaxos/dlog"
	"github.com/imdea-software/swiftpaxos-epaxos/replica/defs"
)

// TestNewWithoutRoute builds a replica as the deployment does (no latency file:
// defs.LatencyConf is "") on a host with no route: the test runs itself again in a new,
// empty network namespace (unshare -n: only a down lo, no route), where the child calls New.
// New must not need the network (U1: it dialed UDP to 8.8.8.8 for an address it does not use,
// and dereferenced the nil connection when the dial failed).
func TestNewWithoutRoute(t *testing.T) {
	if os.Getenv("REPLICA_NOROUTE_CHILD") == "1" {
		if defs.LatencyConf != "" {
			t.Fatal("LatencyConf is set")
		}
		addrs := []string{"10.77.0.12:7002", "10.77.0.13:7003", "10.77.0.14:7004"}
		New("n2", 0, 1, addrs, false, true, false, &config.Config{Proxy: &config.ProxyInfo{}}, &dlog.Logger{})
		return
	}
	if err := exec.Command("unshare", "-n", "true").Run(); err != nil {
		t.Skip("cannot create a network namespace (unshare -n):", err)
	}
	cmd := exec.Command("unshare", "-n", os.Args[0], "-test.run=^TestNewWithoutRoute$", "-test.v")
	cmd.Env = append(os.Environ(), "REPLICA_NOROUTE_CHILD=1")
	out, err := cmd.CombinedOutput()
	if err != nil {
		t.Fatalf("replica.New on a host with no route failed: %v\n%s", err, out)
	}
}
