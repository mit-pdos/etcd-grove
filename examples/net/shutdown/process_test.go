package shutdown

import (
	"testing"
	"time"

	"github.com/mit-pdos/etcd-grove/examples/net/internal/proctest"
)

// TestProcesses runs the node's process (cmd/node, the program of the
// distributed adequacy theorem) again and again: it exits 0 every time (none
// of its checks panics).
func TestProcesses(t *testing.T) {
	bins := proctest.Build(t, "./cmd/node")
	for i := 0; i < 20; i++ {
		proctest.RunOK(t, bins["node"], 20*time.Second)
	}
}
