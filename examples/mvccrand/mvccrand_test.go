package mvccrand

import (
	"path/filepath"
	"testing"
	"time"
)

// TestRun runs many seeds, and waits at the end for every watcher to have every event (a
// liveness check Main does not make).
func TestRun(t *testing.T) {
	events := 0
	var above int64
	for seed := uint64(1); seed <= 30; seed++ {
		rep := Run(Config{Path: filepath.Join(t.TempDir(), "mvccrand.db"), Seed: seed, Ops: 2000,
			Readers: 4, Reads: 400, Watchers: 8, Drain: 10 * time.Second})
		if !rep.WatchersComplete {
			t.Fatalf("seed %d: a watcher did not receive every event", seed)
		}
		events += rep.Events
		above += rep.ReadsAboveFloor
	}
	t.Logf("watch events checked: %d; reads above their floor (concurrent with a write): %d",
		events, above)
}

func TestMain_(t *testing.T) {
	t.Chdir(t.TempDir())
	Main()
}
