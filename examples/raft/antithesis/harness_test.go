package antithesis

import (
	"fmt"
	"os"
	"path/filepath"
	"strconv"
	"testing"
	"time"

	"github.com/mit-pdos/etcd-grove/examples/raft/antithesis/check"
	"github.com/mit-pdos/etcd-grove/examples/raft/antithesis/check/ndjson"
)

// variants are the schedules TestRuns draws from (VARIANT=name for one): DefaultConfig, and others
// that lose more messages, delay them longer, isolate nodes more often or run longer.
func variants() map[string]Config {
	lossy := DefaultConfig()
	lossy.DropPct, lossy.MaxDelay = 30, 10*time.Millisecond
	churn := DefaultConfig()
	churn.Isolations, churn.IsolateFor, churn.Tick = 10, 30*time.Millisecond, time.Millisecond
	long := DefaultConfig()
	long.Proposals, long.ProposeGap = 300, 2*time.Millisecond
	slow := DefaultConfig()
	slow.MaxDelay, slow.Tick = 25*time.Millisecond, 3*time.Millisecond
	return map[string]Config{"default": DefaultConfig(), "lossy": lossy, "churn": churn, "long": long, "slow": slow}
}

// TestRuns runs RUNS clusters (default 5) of each variant (or of VARIANT) and checks each stream.
// KEEP=dir writes every stream there (<variant>-<k>.ndjson), for TLC (check/testdata/tlc-dir.sh).
func TestRuns(t *testing.T) {
	vs := variants()
	names := []string{"default", "lossy", "churn", "long", "slow"}
	if v := os.Getenv("VARIANT"); v != "" {
		names = []string{v}
	}
	for _, name := range names {
		runVariant(t, name, vs[name])
	}
}

func runVariant(t *testing.T, name string, conf Config) {
	runs := 5
	if s := os.Getenv("RUNS"); s != "" {
		runs, _ = strconv.Atoi(s)
	}
	keep := os.Getenv("KEEP")
	accepted := 0
	for k := 1; k <= runs; k++ {
		c := RunCluster(conf)
		evs := c.Events()
		cfg := &check.Config{Server: c.Servers(), InitVoters: c.Servers(), Bootstrapped: false}
		v := check.Check(cfg, evs)
		if keep != "" || v.Kind != check.Accepted {
			dir := keep
			if dir == "" {
				dir = t.TempDir()
			}
			p := filepath.Join(dir, fmt.Sprintf("%s-%d.ndjson", name, k))
			f, err := os.Create(p)
			if err != nil {
				t.Fatal(err)
			}
			if err := ndjson.Write(f, evs); err != nil {
				t.Fatal(err)
			}
			f.Close()
			if v.Kind != check.Accepted {
				t.Errorf("%s run %d: %v (%d events; stream %s)", name, k, v, len(evs), p)
				continue
			}
		}
		accepted++
		t.Logf("%s run %d: %v", name, k, v)
	}
	t.Logf("%s: %d of %d accepted", name, accepted, runs)
}
