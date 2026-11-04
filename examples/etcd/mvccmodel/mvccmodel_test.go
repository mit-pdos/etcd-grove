package mvccmodel

import (
	"flag"
	"path/filepath"
	"testing"
	"time"
)

var (
	seeds = flag.Int("mvccmodel.seeds", 10, "number of seeds to run")
	seed0 = flag.Uint64("mvccmodel.seed", 1, "first seed")
)

// TestMVCCModel runs the randomized test over a range of seeds. A failure names its seed; rerun
// it with -mvccmodel.seed=N -mvccmodel.seeds=1 (the goroutines' interleaving is not reproduced,
// only their operations).
func TestMVCCModel(t *testing.T) {
	for s := *seed0; s < *seed0+uint64(*seeds); s++ {
		cfg := Config{Path: filepath.Join(t.TempDir(), "mvcc.db"), Seed: s, ApplierOps: 2000,
			Readers: 4, Streams: 3, Drain: 20 * time.Second}
		if err := Run(cfg); err != nil {
			t.Fatalf("seed %d: %v", s, err)
		}
	}
}
