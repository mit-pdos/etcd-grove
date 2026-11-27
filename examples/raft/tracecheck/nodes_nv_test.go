//go:build with_tla

package tracecheck

import (
	"testing"

	"github.com/mit-pdos/etcd-grove/examples/raft/tracecheck/etcdraft"
)

// TestMainRandomNodes (rule 38's non-vacuity test for a Main that draws its bootstrap size,
// cfg.Nodes = 1 + below(5)): for every size the generator can draw, runs of Main's path start the
// cluster, read as a trace, and pass raft's TLA+ trace validation, so Main's real path (the check
// the theorem is about) is reached for each size, not only at 3. NODES_SEEDS runs per size (default 3).
func TestMainRandomNodes(t *testing.T) {
	for n := 1; n <= 5; n++ {
		for s := 0; s < envInt("NODES_SEEDS", 3); s++ {
			cfg := DefaultCConfig()
			cfg.Nodes = n
			c, err := RunConcurrent(cfg)
			if err != nil {
				t.Fatalf("nodes %d run %d: the cluster did not start: %v", n, s, err)
			}
			tr, err := etcdraft.NewTrace(ConvertEvents(c.Events()))
			if err != nil {
				t.Fatalf("nodes %d run %d: not a trace the specification reads: %v", n, s, err)
			}
			r := etcdraft.CheckTrace(tr, true)
			t.Logf("nodes %d run %d: %d events, proposed %d, delivered %d: %v", n, s, len(c.Events()),
				c.Proposed.Load(), c.Delivered.Load(), r)
			if !r.TLCOK() {
				t.Errorf("nodes %d run %d: the trace does not pass the TLA+ trace validation: %v", n, s, r)
			}
		}
	}
}
